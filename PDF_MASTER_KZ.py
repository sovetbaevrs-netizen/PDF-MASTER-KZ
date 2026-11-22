"""PDF MASTER KZ — постраничный редактор PDF (Windows / Tkinter).

Установка: py -3.12 -m pip install --upgrade pymupdf pillow
Запуск:    py -3.12 pdf_manual_rotate.py

Не растеризует страницы при сохранении. Миниатюры и предпросмотр создаются
только для небольшого окна страниц. Проект автосохранения — JSON рядом с PDF.
"""
from __future__ import annotations

import json
import os
import math
import tempfile
import threading
import queue
import hashlib
import shutil
import time
import traceback
import tkinter as tk
from dataclasses import dataclass, replace
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk
from PIL import Image, ImageTk, ImageDraw
import pymupdf as fitz

IMAGES = {'.jpg', '.jpeg', '.png', '.bmp', '.tif', '.tiff'}
AUTOSAVE_VERSION = 3
VERSION = '5.2.0'
AUTHOR = 'Советбаев Роллан'
COMPANY = 'ИП «INTERHOST»'
SUPPORT_EMAIL = 'support@coolkaz.kz'
MAX_UNDO = 45


def parse_numbers(value: str, maximum: int, preserve_order=False) -> list[int]:
    """Convert 1-based '5,96,10-13' to 0-based indexes."""
    if not value.strip():
        raise ValueError('Введите номера страниц, например 5, 96 или 10-13')
    result = []
    for chunk in value.replace(';', ',').split(','):
        chunk = chunk.strip()
        if not chunk:
            raise ValueError('Пустой номер страницы')
        if '-' in chunk:
            pair = chunk.split('-')
            if len(pair) != 2:
                raise ValueError(f'Неверный диапазон: {chunk}')
            a, b = (int(x.strip()) for x in pair)
            if a > b:
                raise ValueError(f'Диапазон не по возрастанию: {chunk}')
            vals = range(a, b + 1)
        else:
            vals = (int(chunk),)
        for n in vals:
            if not 1 <= n <= maximum:
                raise ValueError(f'Номер {n} вне диапазона 1–{maximum}')
            if n - 1 in result:
                raise ValueError(f'Повтор номера: {n}')
            result.append(n - 1)
    return result if preserve_order else sorted(result)


@dataclass(frozen=True)
class PageRef:
    path: str
    page: int
    rotation: int    # absolute rotation of PDF page: 0/90/180/270
    crop: tuple | None = None  # (x0,y0,x1,y1) in original PDF coordinates
    annotations: tuple = ()  # JSON overlay instructions, retained in history/autosave

    def json(self):
        return {'path': self.path, 'page': self.page, 'rotation': self.rotation, 'crop': self.crop, 'annotations': list(self.annotations)}


class PdfSourceStore:
    """Source PDFs remain open (no rendering) until a document is closed."""
    def __init__(self):
        self.docs = {}

    def get(self, path):
        path = str(Path(path).resolve())
        if path not in self.docs:
            if not Path(path).is_file():
                raise FileNotFoundError(f'Не найден файл: {path}')
            if Path(path).suffix.lower() in IMAGES:
                with fitz.open(path) as image:
                    pdfbytes = image.convert_to_pdf()
                doc = fitz.open(stream=pdfbytes, filetype='pdf')
            else:
                doc = fitz.open(path)
                if not doc.is_pdf:
                    doc.close()
                    raise ValueError('Нужен PDF или файл изображения')
            if doc.needs_pass:
                doc.close()
                raise ValueError(f'Файл защищён паролем: {path}')
            if not doc.page_count:
                doc.close()
                raise ValueError(f'Файл без страниц: {path}')
            self.docs[path] = doc
        return self.docs[path]

    def close(self):
        for doc in self.docs.values():
            try:
                doc.close()
            except Exception:
                pass
        self.docs.clear()


class Editor:
    def __init__(self, root):
        self.root = root
        root.title(f'PDF MASTER KZ {VERSION} — редактор PDF')
        root.geometry('1450x900')
        root.minsize(1060, 680)
        self.store = PdfSourceStore()
        self.original_path = None
        self.pages: list[PageRef] = []
        self.current = 0
        self.history: list[tuple[list[PageRef], int]] = []
        self.future: list[tuple[list[PageRef], int]] = []
        self.changed = False
        self.zoom = 1.0
        self.preview_photo = None
        self.thumb_photos = []
        self.thumb_start = 0
        self.thumb_window = 18
        self.thumb_columns = 2
        self.thumb_cell_h = 142
        self.thumb_cache = {}
        self.thumb_update = None
        self.thumb_visible_keys = None
        self.render_task = None
        self.scan_task = None
        self.autosave_task = None
        self.scan_cursor = 0
        self.suspects = {}  # (path,page,rotation) => reason or None
        self.status = tk.StringVar(value='Откройте PDF, чтобы начать')
        self.page_var = tk.StringVar(value='1')
        self.info = tk.StringVar(value='Просмотр загружает одну страницу за раз')
        self.scan_info = tk.StringVar(value='Автопроверка: не запущена')
        self.show_suspects = tk.BooleanVar(value=False)
        self.theme_mode = tk.StringVar(value='light')
        self.grid_mode = False
        self._style()
        self._ui()
        root.protocol('WM_DELETE_WINDOW', self.quit)
        for key, handler in (
            ('<Control-o>', self.open_pdf), ('<Control-s>', self.save_pdf),
            ('<Control-z>', self.undo), ('<Control-y>', self.redo),
            ('<Control-Shift-Z>', self.redo),
            ('<Alt-Left>', lambda: self.rotate(-90)),
            ('<Alt-Right>', lambda: self.rotate(90)),
            ('<Prior>', lambda: self.goto(self.current-1)),
            ('<Next>', lambda: self.goto(self.current+1))):
            root.bind_all(key, lambda e, fn=handler: fn())

    def _style(self):
        dark = self.theme_mode.get() == 'dark'
        self.bg = '#111B27' if dark else '#F0F5FB'
        self.side = '#162434' if dark else '#FFFFFF'
        self.ink = '#EAF1FB' if dark else '#192B41'
        self.muted = '#A7B6C8' if dark else '#5D7088'
        self.accent = '#14C4C4' if dark else '#1672DF'
        self.accent_fg = '#071B23' if dark else '#FFFFFF'
        self.toolbar_bg = '#142231' if dark else '#FFFFFF'
        self.surface = '#1B2B3E' if dark else '#F6F9FD'
        self.viewer_bg = '#0D1723' if dark else '#DEE8F4'
        self.border_color = '#30435A' if dark else '#D8E3F0'
        self.word_blue = self.accent
        self.root.configure(bg=self.bg)
        style = ttk.Style(self.root)
        if 'clam' in style.theme_names(): style.theme_use('clam')
        style.configure('.', font=('Segoe UI', 10), background=self.bg, foreground=self.ink)
        style.configure('TFrame', background=self.bg)
        style.configure('TLabel', background=self.bg, foreground=self.ink)
        style.configure('TButton', padding=(9, 7), background=self.surface, foreground=self.ink,
                        bordercolor=self.border_color)
        style.map('TButton', background=[('active', self.border_color)])
        style.configure('Accent.TButton', padding=(10, 7), background=self.accent,
                        foreground=self.accent_fg, font=('Segoe UI', 10, 'bold'))
        style.map('Accent.TButton', background=[('active', self.accent)])
        style.configure('TEntry', padding=5, fieldbackground=self.side, foreground=self.ink)
        style.configure('TLabelframe', background=self.bg)
        style.configure('TLabelframe.Label', background=self.bg, foreground=self.ink)
        style.configure('Vertical.TScrollbar', background=self.surface, troughcolor=self.bg)
        style.configure('Horizontal.TScrollbar', background=self.surface, troughcolor=self.bg)
        self.ribbon_images = {}

    def _button(self, parent, title, cmd, accent=False):
        return ttk.Button(parent, text=title, command=cmd,
                          style='Accent.TButton' if accent else 'TButton')

    def _flatbutton(self, parent, label, command, icon=None, selected=False, compact=False):
        bg = self.surface if selected else self.toolbar_bg
        fg = self.accent if selected else self.ink
        b = tk.Button(parent, text=label,
                      image=self._icon(icon, 21 if compact else 24) if icon else None,
                      compound='left' if icon else 'none', command=command,
                      font=('Segoe UI', 9, 'bold' if selected else 'normal'),
                      bg=bg, fg=fg, activebackground=self.surface,
                      activeforeground=self.accent, bd=0, relief='flat',
                      cursor='hand2', padx=9, pady=7)
        b.pack(side='left', padx=2, pady=3)
        return b

    def set_theme(self, mode):
        if mode not in ('light','dark') or self.theme_mode.get()==mode: return
        was_grid = self.grid_mode
        self.grid_mode = False
        self.theme_mode.set(mode)
        self.stop_tasks()
        for child in list(self.root.winfo_children()): child.destroy()
        self.preview_photo = None
        self.thumb_photos.clear()
        self.thumb_cache.clear()
        self._style()
        self._ui()
        self.sync_view()
        if was_grid: self.toggle_grid()
        if self.changed: self.schedule_autosave()
        self.status.set('Тема изменена · документ и изменения сохранены')

    def toggle_grid(self):
        self.grid_mode = not self.grid_mode
        self.grid_frame.pack_forget()
        self.viewer_frame.pack_forget()
        if self.grid_mode:
            self.grid_frame.pack(fill='both',expand=True)
            self.show_grid()
        else:
            self.viewer_frame.pack(fill='both',expand=True)
            self.schedule_render()
        self.grid_switch.configure(text='☷  Страница' if self.grid_mode else '▦  Сетка')

    def show_grid(self):
        if not self.grid_mode: return
        for widget in self.grid_items.winfo_children(): widget.destroy()
        self.grid_photos=[]
        if not self.pages: return
        batch=30
        first=(self.current//batch)*batch
        self.grid_label.configure(text=f'Обзор страниц: {first+1}–{min(len(self.pages),first+batch)} из {len(self.pages)}')
        for offset, i in enumerate(range(first,min(len(self.pages),first+batch))):
            r,c=divmod(offset,6)
            f=tk.Frame(self.grid_items,bg=self.surface if i==self.current else self.bg,
                       highlightbackground=self.accent if i==self.current else self.border_color,
                       highlightthickness=2 if i==self.current else 1)
            f.grid(row=r,column=c,padx=9,pady=9,sticky='n')
            try:
                img=self.render_ref(self.pages[i],110,140)
                photo=ImageTk.PhotoImage(img)
                self.grid_photos.append(photo)
                label=tk.Label(f,image=photo,bg=self.surface if i==self.current else self.bg,
                               cursor='hand2')
                label.pack(padx=8,pady=(8,2))
                label.bind('<Button-1>',lambda e,n=i:self._grid_select(n))
            except Exception:
                tk.Label(f,text='Ошибка просмотра',bg=self.bg,fg=self.ink).pack(padx=8,pady=25)
            b=tk.Button(f,text=f'{i+1}',bg=self.surface if i==self.current else self.bg,
                        fg=self.accent if i==self.current else self.ink,relief='flat',bd=0,
                        command=lambda n=i:self._grid_select(n))
            b.pack(pady=2)

    def _grid_select(self, index):
        self.goto(index)
        if self.grid_mode:self.toggle_grid()

    def grid_shift(self, amount):
        if not self.pages:return
        self.goto(max(0,min(len(self.pages)-1,(self.current//30+amount)*30)))
        self.show_grid()

    def _icon(self, kind, size=33):
        """Independent, Word-like vector icons; no external icon assets or font required."""
        key = (kind, size)
        if key in self.ribbon_images:
            return self.ribbon_images[key]
        scale = 3
        n = size * scale
        im = Image.new('RGBA', (n, n), (255,255,255,0))
        d = ImageDraw.Draw(im)
        blue = '#185ABD'
        navy = '#2B579A'
        grey = '#5D6876'
        green = '#16835F'
        red = '#B42332'
        def pt(x,y): return (int(x*n/40), int(y*n/40))
        def line(coords, fill=blue, width=2.3):
            d.line([pt(*p) for p in coords], fill=fill, width=max(2,int(width*n/40)), joint='curve')
        def rect(x1,y1,x2,y2,outline=blue,fill=None,width=2):
            d.rectangle([pt(x1,y1),pt(x2,y2)],outline=outline,fill=fill,width=max(2,int(width*n/40)))
        def oval(x1,y1,x2,y2,outline=blue,fill=None,width=2):
            d.ellipse([pt(x1,y1),pt(x2,y2)],outline=outline,fill=fill,width=max(2,int(width*n/40)))
        def paper(x=10,y=4,w=21,h=30):
            rect(x,y,x+w,y+h,outline=navy,fill='white',width=2)
            line([(x+4,y+9),(x+w-4,y+9)],grey,1.5)
            line([(x+4,y+14),(x+w-4,y+14)],grey,1.5)
            line([(x+4,y+19),(x+w-4,y+19)],grey,1.5)
        if kind in ('open','insert','replace','copy'):
            if kind == 'open':
                rect(4,16,33,33,outline=navy,fill='#DBEAFE')
                line([(5,14),(5,10),(17,10),(21,14),(34,14)],blue,2)
                line([(4,33),(11,19),(37,19),(31,33)],blue,2)
            else:
                paper(7,4,21,29)
                if kind=='insert':
                    line([(29,28),(38,28)],green,3)
                    line([(33.5,23),(33.5,33)],green,3)
                elif kind=='replace':
                    line([(27,24),(37,24),(37,32)],green,2.6)
                    line([(37,32),(32,28)],green,2.6)
                    line([(37,32),(40,27)],green,2.6)
                else:
                    rect(13,10,34,38,outline=blue,fill=None)
        elif kind in ('save','saveas'):
            rect(7,5,33,35,outline=navy,fill='#DBEAFE')
            rect(12,6,28,16,outline=navy,fill='white')
            rect(12,22,28,34,outline=blue,fill='white')
            if kind=='saveas': line([(23,29),(37,15)],green,3)
        elif kind in ('undo','redo','left','right'):
            cw = kind in ('redo','right')
            # circular arc and arrowhead
            bbox = (*pt(8,7),*pt(32,32))
            d.arc(bbox, start=230 if cw else 5, end=525 if cw else 300, fill=blue, width=7)
            if cw:
                line([(28,10),(33,11),(35,19)],blue,3)
            else:
                line([(12,10),(7,12),(6,19)],blue,3)
        elif kind=='flip':
            paper(11,4,19,32)
            line([(5,11),(10,6),(15,11)],green,2.5)
            line([(35,29),(30,34),(25,29)],green,2.5)
        elif kind=='reset':
            paper(10,6,21,29)
            line([(4,13),(9,8),(14,13)],green,2.5)
        elif kind in ('delete','delete_many'):
            rect(12,13,29,34,outline=red,fill='#FDEBEC')
            line([(9,10),(32,10)],red,3)
            line([(16,6),(25,6)],red,2.5)
            line([(17,17),(17,29)],red,2)
            line([(24,17),(24,29)],red,2)
            if kind=='delete_many': rect(4,19,9,32,outline=red,fill='#FDEBEC')
        elif kind == 'move':
            paper(10,5,20,29)
            line([(3,20),(35,20)],green,2.5)
            line([(30,15),(35,20),(30,25)],green,2.5)
        elif kind in ('scan','find'):
            paper(7,4,22,29)
            oval(20,19,34,33,blue,'white',2.5)
            line([(31,31),(38,38)],blue,3.5)
        elif kind=='compare':
            rect(3,8,20,34,outline=blue,fill='#E8F0FC')
            rect(22,8,39,34,outline=navy,fill='#DCE8F8')
            line([(7,15),(16,15)],grey)
            line([(26,15),(35,15)],grey)
        elif kind=='previous':
            line([(27,6),(12,20),(27,34)],blue,4)
        elif kind=='next':
            line([(13,6),(28,20),(13,34)],blue,4)
        elif kind in ('zoom_in','zoom_out'):
            oval(4,4,27,27,blue,'white',2.5)
            line([(25,25),(37,37)],blue,3.5)
            line([(10,16),(21,16)],blue,2.5)
            if kind=='zoom_in': line([(15.5,10),(15.5,22)],blue,2.5)
        elif kind=='fit':
            rect(6,7,34,33,outline=blue)
            line([(14,15),(10,11)],green)
            line([(26,15),(30,11)],green)
            line([(14,25),(10,29)],green)
            line([(26,25),(30,29)],green)
        elif kind=='crop':
            paper()
            line([(4,15),(4,4),(15,4)],green,3)
            line([(25,36),(36,36),(36,25)],green,3)
        elif kind=='merge':
            paper(3,5,16,28)
            paper(21,8,16,28)
        elif kind=='compress':
            paper()
            line([(5,20),(17,20),(17,27)],green,3)
            line([(35,20),(23,20),(23,13)],green,3)
        elif kind=='help':
            oval(7,7,33,33,blue,'white',3)
            d.text(pt(14,7),'?',fill=blue,stroke_width=0)
        else:
            paper()
        im = im.resize((size,size),Image.Resampling.LANCZOS)
        photo = ImageTk.PhotoImage(im)
        self.ribbon_images[key] = photo
        return photo

    def _ui(self):
        # One-line header, compact primary commands, permanent page navigation.
        header=tk.Frame(self.root,bg=self.toolbar_bg,height=49)
        header.pack(fill='x')
        header.pack_propagate(False)
        tk.Label(header,text='▣',font=('Segoe UI',18,'bold'),bg=self.toolbar_bg,
                 fg=self.accent).pack(side='left',padx=(17,6))
        tk.Label(header,text='PDF MASTER KZ',font=('Segoe UI',12,'bold'),
                 bg=self.toolbar_bg,fg=self.ink).pack(side='left')
        tk.Label(header,text=f'  •  {VERSION}',font=('Segoe UI',9),
                 bg=self.toolbar_bg,fg=self.muted).pack(side='left')
        self._flatbutton(header,'?',self.show_help).pack_configure(side='right',padx=(0,10))
        self._flatbutton(header,'О программе',self.show_about).pack_configure(side='right')
        self._flatbutton(header,'☀  Светлая',lambda:self.set_theme('light'),
                         selected=self.theme_mode.get()=='light').pack_configure(side='right')
        self._flatbutton(header,'☾  Тёмная',lambda:self.set_theme('dark'),
                         selected=self.theme_mode.get()=='dark').pack_configure(side='right')

        bar=tk.Frame(self.root,bg=self.toolbar_bg)
        bar.pack(fill='x')
        for label,fn,ic in [
            ('Открыть',self.open_pdf,'open'),('Сохранить',self.save_pdf,'save'),
            ('Отменить',self.undo,'undo'),('Повторить',self.redo,'redo'),
            ('Вставить',self.insert_pages,'insert'),('Заменить',self.replace_current,'replace'),
            ('Удалить',self.delete_current,'delete'),
            ('↶ 90°',lambda:self.rotate(-90),'left'),('↷ 90°',lambda:self.rotate(90),'right'),
            ('Обрезать',self.crop_current,'crop')]:
            self._flatbutton(bar,label,fn,ic,compact=True)
        self._flatbutton(bar,'Все инструменты ▾',self._file_menu).pack_configure(side='right',padx=8)
        tk.Frame(self.root,bg=self.border_color,height=1).pack(fill='x')

        workspace=tk.PanedWindow(self.root,orient='horizontal',sashwidth=5,
                                 bg=self.border_color,bd=0,relief='flat')
        workspace.pack(fill='both',expand=True)
        left=tk.Frame(workspace,bg=self.side,width=190)
        left.pack_propagate(False)
        workspace.add(left,minsize=135,width=192)
        tk.Label(left,text='СТРАНИЦЫ',bg=self.side,fg=self.ink,
                 font=('Segoe UI',10,'bold'),anchor='w').pack(fill='x',padx=12,pady=(13,3))
        self.thumb_text=tk.Label(left,text='Откройте PDF',bg=self.side,fg=self.muted,
                                 font=('Segoe UI',9),anchor='w')
        self.thumb_text.pack(fill='x',padx=12,pady=(0,7))
        thumbs=tk.Frame(left,bg=self.side)
        thumbs.pack(fill='both',expand=True)
        self.thumb_canvas=tk.Canvas(thumbs,bg=self.side,highlightthickness=0,width=175)
        self.thumb_scroll=ttk.Scrollbar(thumbs,orient='vertical',command=self._thumb_scroll)
        self.thumb_canvas.configure(yscrollcommand=self.thumb_scroll.set)
        self.thumb_canvas.bind('<Configure>',lambda e:self._schedule_thumb_refresh())
        self.thumb_canvas.bind('<MouseWheel>',self._thumb_wheel)
        self.thumb_canvas.bind('<Button-4>',lambda e:self._thumb_scroll('scroll',-3,'units'))
        self.thumb_canvas.bind('<Button-5>',lambda e:self._thumb_scroll('scroll',3,'units'))
        self.thumb_scroll.pack(side='right',fill='y')
        self.thumb_canvas.pack(fill='both',expand=True)
        self.thumb_columns=1
        self.thumb_cell_h=138
        self.thumb_inner=None

        center=tk.Frame(workspace,bg=self.viewer_bg)
        workspace.add(center,minsize=400,stretch='always')
        strip=tk.Frame(center,bg=self.toolbar_bg)
        strip.pack(fill='x')
        self.grid_switch=self._flatbutton(strip,'▦  Сетка',self.toggle_grid)
        self._flatbutton(strip,'Проверка ↗',self.start_scan).pack_configure(side='right',padx=8)
        self._flatbutton(strip,'Следующая ⚠',self.next_suspect).pack_configure(side='right')
        self.viewer_frame=tk.Frame(center,bg=self.viewer_bg)
        self.viewer_frame.pack(fill='both',expand=True)
        self.viewer=tk.Canvas(self.viewer_frame,bg=self.viewer_bg,highlightthickness=0)
        vs=ttk.Scrollbar(self.viewer_frame,orient='vertical',command=self.viewer.yview)
        hs=ttk.Scrollbar(self.viewer_frame,orient='horizontal',command=self.viewer.xview)
        self.viewer.configure(yscrollcommand=vs.set,xscrollcommand=hs.set)
        vs.pack(side='right',fill='y')
        hs.pack(side='bottom',fill='x')
        self.viewer.pack(side='left',fill='both',expand=True)
        self.viewer.bind('<Configure>',lambda e:self.schedule_render())
        self.viewer.bind('<MouseWheel>',lambda e:self.viewer.yview_scroll(-int(e.delta/120)*3,'units'))
        self.viewer.bind('<Button-4>',lambda e:self.viewer.yview_scroll(-3,'units'))
        self.viewer.bind('<Button-5>',lambda e:self.viewer.yview_scroll(3,'units'))
        self.grid_frame=tk.Frame(center,bg=self.bg)
        gbar=tk.Frame(self.grid_frame,bg=self.bg)
        gbar.pack(fill='x')
        self.grid_label=tk.Label(gbar,text='Сетка страниц',bg=self.bg,fg=self.ink)
        self.grid_label.pack(side='left',padx=12,pady=8)
        self._button(gbar,'Следующие 30 →',lambda:self.grid_shift(1)).pack(side='right',padx=8)
        self._button(gbar,'← Предыдущие 30',lambda:self.grid_shift(-1)).pack(side='right')
        self.grid_items=tk.Frame(self.grid_frame,bg=self.bg)
        self.grid_items.pack(expand=True,anchor='center')

        right=tk.Frame(workspace,bg=self.side,width=237)
        workspace.add(right,minsize=175,width=240)
        tk.Label(right,text='ДЕЙСТВИЯ',bg=self.side,fg=self.ink,
                 font=('Segoe UI',11,'bold'),anchor='w').pack(fill='x',padx=14,pady=(15,8))
        self._side_group(right,'Страница',[
            ('↶  Повернуть влево',lambda:self.rotate(-90)),
            ('↷  Повернуть вправо',lambda:self.rotate(90)),
            ('⟳  Повернуть на 180°',lambda:self.rotate(180)),
            ('⇄  Заменить страницу',self.replace_current),
            ('⊞  Заменить несколько',self.replace_many),
            ('＋  Вставить страницы',self.insert_pages),
            ('↕  Переместить страницу',self.move_page),
            ('✕  Удалить страницу',self.delete_current),
            ('⌫  Удалить диапазон',self.delete_many),
            ('⌗  Обрезать страницу',self.crop_current)])
        self._side_group(right,'Инструменты PDF',[
            ('⊞  Объединить PDF',self.merge_pdfs),
            ('▧  JPG / PNG → PDF',self.images_to_pdf),
            ('⇣  Сжать PDF',self.compress_pdf),
            ('✓  Проверить ориентацию',self.start_scan)])
        self._side_group(right,'Информация',[
            ('?  Руководство',self.show_help),
            ('ⓘ  Лицензия',self.show_license)])

        bottom=tk.Frame(self.root,bg=self.toolbar_bg,height=40)
        bottom.pack(fill='x')
        self._flatbutton(bottom,'◀',lambda:self.goto(self.current-1))
        self.page_entry=ttk.Entry(bottom,textvariable=self.page_var,width=7,justify='center')
        self.page_entry.pack(side='left',padx=4)
        self.page_entry.bind('<Return>',lambda e:self.jump())
        self.count_label=tk.Label(bottom,text='из 0',bg=self.toolbar_bg,fg=self.ink)
        self.count_label.pack(side='left',padx=5)
        self._flatbutton(bottom,'▶',lambda:self.goto(self.current+1))
        self._flatbutton(bottom,'−',lambda:self.change_zoom(-.15)).pack_configure(side='right',padx=(0,12))
        self.zoom_label=tk.Label(bottom,text='100%',bg=self.toolbar_bg,fg=self.ink)
        self.zoom_label.pack(side='right',padx=4)
        self._flatbutton(bottom,'+',lambda:self.change_zoom(.15)).pack_configure(side='right')
        self._flatbutton(bottom,'По размеру',self.fit_page).pack_configure(side='right')
        tk.Label(bottom,textvariable=self.info,bg=self.toolbar_bg,fg=self.muted,
                 font=('Segoe UI',9),anchor='w').pack(side='left',padx=12,fill='x',expand=True)
        foot=tk.Frame(self.root,bg=self.surface,height=24)
        foot.pack(fill='x')
        tk.Label(foot,textvariable=self.status,bg=self.surface,fg=self.ink,font=('Segoe UI',9),
                 anchor='w').pack(side='left',fill='x',expand=True,padx=10)
        tk.Label(foot,textvariable=self.scan_info,bg=self.surface,fg=self.muted,
                 font=('Segoe UI',9)).pack(side='right',padx=10)
        self.root.update_idletasks()

    def _side_group(self,parent,name,items):
        tk.Label(parent,text=name.upper(),bg=self.side,fg=self.muted,
                 font=('Segoe UI',9,'bold'),anchor='w').pack(fill='x',padx=14,pady=(10,4))
        for label,fn in items:
            btn=tk.Button(parent,text=label,command=fn,anchor='w',relief='flat',bd=0,
                          font=('Segoe UI',9),bg=self.surface,fg=self.ink,
                          activebackground=self.border_color,activeforeground=self.accent,
                          cursor='hand2',padx=10,pady=5)
            btn.pack(fill='x',padx=10,pady=2)

    def _file_menu(self):
        menu=tk.Menu(self.root,tearoff=False,font=('Segoe UI',10))
        menu.add_command(label='Открыть PDF…        Ctrl+O',command=self.open_pdf)
        menu.add_command(label='Сохранить как…     Ctrl+S',command=self.save_pdf)
        menu.add_command(label='Заменить несколько страниц…',command=self.replace_many)
        menu.add_command(label='Удалить несколько страниц…',command=self.delete_many)
        menu.add_command(label='Переместить страницу…',command=self.move_page)
        menu.add_separator()
        menu.add_command(label='Проверить ориентацию',command=self.start_scan)
        menu.add_command(label='Обрезать страницу…',command=self.crop_current)
        menu.add_command(label='Объединить PDF…',command=self.merge_pdfs)
        menu.add_command(label='Изображения в PDF…',command=self.images_to_pdf)
        menu.add_command(label='Сжатие PDF…',command=self.compress_pdf)
        menu.add_separator()
        menu.add_command(label='Справка',command=self.show_help)
        menu.add_command(label='Лицензия',command=self.show_license)
        menu.add_command(label='О программе',command=self.show_about)
        menu.add_separator()
        menu.add_command(label='Выход',command=self.quit)
        menu.tk_popup(self.root.winfo_rootx()+8,self.root.winfo_rooty()+92)
        menu.grab_release()

    def needs_doc(self):
        if self.pages:
            return True
        messagebox.showinfo('PDF', 'Сначала откройте PDF')
        return False

    def stop_tasks(self):
        for name in ('render_task', 'scan_task', 'autosave_task', 'thumb_update'):
            job = getattr(self, name)
            if job is not None:
                try:
                    self.root.after_cancel(job)
                except tk.TclError:
                    pass
                setattr(self, name, None)

    def reset_document(self):
        self.stop_tasks()
        self.store.close()
        self.pages = []
        self.history.clear()
        self.future.clear()
        self.suspects.clear()
        self.changed = False
        self.scan_cursor = 0
        self.preview_photo = None
        self.thumb_photos.clear()
        self.thumb_cache.clear()
        self.thumb_visible_keys = None
        self.viewer.delete('all')
        self.clear_thumbs()

    def autosave_path(self):
        return Path(str(self.original_path) + '.manualrotator.autosave.json')

    def source_signature(self):
        p = self.original_path
        st = p.stat()
        return {'size': st.st_size, 'mtime_ns': st.st_mtime_ns}

    def open_pdf(self):
        if self.changed and not messagebox.askyesno('Несохранённые правки', 'Открыть другой файл? Текущий проект останется в файле автовосстановления.'):
            return
        path = filedialog.askopenfilename(title='Выберите PDF', filetypes=[('PDF', '*.pdf')])
        if not path:
            return
        self.load_pdf(path)

    def load_pdf(self, path):
        try:
            path = str(Path(path).resolve())
            store = PdfSourceStore()
            doc = store.get(path)
            items = [PageRef(path, i, doc[i].rotation) for i in range(doc.page_count)]
        except Exception as exc:
            try: store.close()
            except Exception: pass
            messagebox.showerror('Ошибка открытия', str(exc))
            return
        self.reset_document()
        self.store = store
        self.original_path = Path(path)
        self.pages = items
        self.current = 0
        recovery_path = self.autosave_path()
        if recovery_path.exists():
            try:
                data = json.loads(recovery_path.read_text(encoding='utf-8'))
                if data.get('version') != AUTOSAVE_VERSION or data.get('signature') != self.source_signature():
                    self.status.set('Старое автосохранение не соответствует исходному файлу и пропущено')
                elif messagebox.askyesno('Восстановление', 'Найден автосохранённый проект. Восстановить изменения?'):
                    restored = [PageRef(**p) for p in data['pages']]
                    for entry in restored:
                        src = self.store.get(entry.path)
                        if not 0 <= entry.page < src.page_count or entry.rotation not in (0,90,180,270):
                            raise ValueError('Некорректные данные проекта')
                    if not restored:
                        raise ValueError('Проект без страниц')
                    self.pages = restored
                    self.current = min(max(0, int(data.get('current', 0))), len(restored)-1)
                    self.changed = True
            except Exception as ex:
                messagebox.showwarning('Восстановление', f'Не удалось восстановить проект:\n{ex}')
        self.root.title(f'PDF MASTER KZ {VERSION} — {self.original_path.name}')
        self.sync_view()
        self.status.set(f'Открыто: {path} | {len(self.pages)} страниц')
        if self.changed:
            self.schedule_autosave()

    def snapshot(self):
        self.history.append((self.pages.copy(), self.current))
        if len(self.history) > MAX_UNDO:
            self.history.pop(0)
        self.future.clear()

    def commit(self, new_pages, new_current, desc):
        if not new_pages:
            messagebox.showwarning('Операция отменена', 'Нельзя оставить PDF без страниц')
            return
        self.snapshot()
        self.pages = new_pages
        self.current = max(0, min(new_current, len(new_pages)-1))
        self.changed = True
        self.suspects.clear()  # orientation review must be recomputed
        self.scan_cursor = 0
        self.sync_view()
        self.status.set(desc)
        self.schedule_autosave()

    def undo(self):
        if not self.history:
            self.root.bell()
            return
        self.future.append((self.pages.copy(), self.current))
        self.pages, self.current = self.history.pop()
        self.changed = True
        self.suspects.clear()
        self.scan_cursor = 0
        self.sync_view()
        self.status.set('Действие отменено (Ctrl+Y — повторить)')
        self.schedule_autosave()

    def redo(self):
        if not self.future:
            self.root.bell()
            return
        self.history.append((self.pages.copy(), self.current))
        self.pages, self.current = self.future.pop()
        self.changed = True
        self.suspects.clear()
        self.scan_cursor = 0
        self.sync_view()
        self.status.set('Действие повторено')
        self.schedule_autosave()

    def schedule_autosave(self):
        if self.autosave_task is not None:
            self.root.after_cancel(self.autosave_task)
        self.autosave_task = self.root.after(1200, self.write_autosave)

    def write_autosave(self):
        self.autosave_task = None
        if not self.changed or not self.original_path:
            return
        dest = self.autosave_path()
        tmp = None
        try:
            data = {'version': AUTOSAVE_VERSION, 'signature': self.source_signature(),
                    'current': self.current, 'pages': [p.json() for p in self.pages]}
            with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', dir=str(dest.parent),
                                             prefix='.pdfmaster_', suffix='.tmp', delete=False) as f:
                tmp = f.name
                json.dump(data, f, ensure_ascii=False)
            os.replace(tmp, dest)
        except Exception as ex:
            self.status.set(f'Автосохранение не удалось: {ex}')
            if tmp and os.path.exists(tmp):
                os.unlink(tmp)

    def ref_page(self, ref):
        return self.store.get(ref.path)[ref.page]

    def dimensions(self, ref):
        page = self.ref_page(ref)
        rect = fitz.Rect(ref.crop) if ref.crop else page.cropbox
        width, height = rect.width, rect.height
        # page.rect reflects source rotation; mediabox is physical page box
        if ref.rotation % 180:
            return height, width
        return width, height

    def rotate(self, degrees):
        if not self.needs_doc(): return
        p = self.pages[self.current]
        new = self.pages.copy()
        new[self.current] = replace(p, rotation=(p.rotation+degrees)%360)
        self.commit(new, self.current, f'Страница {self.current+1}: поворот {degrees:+}°')

    def reset_rotation(self):
        if not self.needs_doc(): return
        p = self.pages[self.current]
        original = self.ref_page(p).rotation
        if original == p.rotation: return
        new = self.pages.copy()
        new[self.current] = replace(p, rotation=original)
        self.commit(new, self.current, 'Сброшен поворот страницы')

    def goto(self, i):
        if not self.pages: return
        if i < 0 or i >= len(self.pages):
            self.root.bell()
            return
        self.current = i
        self.sync_view()
        if self.changed: self.schedule_autosave()

    def jump(self):
        if not self.needs_doc(): return
        try:
            self.goto(int(self.page_var.get())-1)
        except ValueError:
            messagebox.showwarning('Страница', 'Введите номер страницы')

    def sync_view(self):
        if not self.pages: return
        self.page_var.set(str(self.current+1))
        self.count_label.configure(text=f'из {len(self.pages)}')
        self.schedule_render()
        self._focus_thumb(self.current)
        self.refresh_thumbs()
        self.page_hint()

    def change_zoom(self, delta):
        self.zoom = max(.3, min(3, self.zoom+delta))
        self.zoom_label.configure(text=f'{round(self.zoom*100)}%')
        self.schedule_render()

    def fit_page(self):
        self.zoom = 1.0
        self.zoom_label.configure(text='100%')
        self.schedule_render()

    def schedule_render(self, event=None):
        if self.render_task is not None:
            self.root.after_cancel(self.render_task)
        self.render_task = self.root.after(120, self.render)

    def render_ref(self, ref, max_width, max_height):
        page = self.ref_page(ref)
        w, h = self.dimensions(ref)
        scale = min(max_width/max(w,1), max_height/max(h,1))
        # source display rotation is replaced temporarily, restored immediately
        original = page.rotation
        if ref.crop is not None:
            # Do not mutate source document's cropbox during preview.
            with fitz.open() as preview_doc:
                preview_doc.insert_pdf(self.store.get(ref.path), from_page=ref.page, to_page=ref.page)
                temp = preview_doc[0]
                temp.set_cropbox(fitz.Rect(ref.crop))
                temp.set_rotation(ref.rotation)
                pix = temp.get_pixmap(matrix=fitz.Matrix(scale,scale), alpha=False, colorspace=fitz.csRGB)
                return Image.frombytes('RGB',(pix.width,pix.height),pix.samples)
        try:
            if original != ref.rotation:
                page.set_rotation(ref.rotation)
            pix = page.get_pixmap(matrix=fitz.Matrix(scale, scale), alpha=False, colorspace=fitz.csRGB)
            return Image.frombytes('RGB', (pix.width, pix.height), pix.samples)
        finally:
            if page.rotation != original:
                page.set_rotation(original)

    def render(self):
        self.render_task = None
        if self.grid_mode: return
        self.viewer.delete('all')
        if not self.pages: return
        ref = self.pages[self.current]
        try:
            cw = max(280, self.viewer.winfo_width()-36)
            ch = max(360, self.viewer.winfo_height()-36)
            img = self.render_ref(ref, min(cw*self.zoom, 2400), min(ch*self.zoom, 3200))
            self.preview_photo = ImageTk.PhotoImage(img)
            width, height = img.size
            area_w = max(cw+36, width+36)
            area_h = max(ch+36, height+36)
            self.viewer.config(scrollregion=(0, 0, area_w, area_h))
            x = max(18, (area_w-width)//2)
            y = max(18, (area_h-height)//2)
            self.viewer.create_rectangle(x+4, y+5, x+width+4, y+height+5, fill=self.border_color, outline='')
            self.viewer.create_image(x, y, image=self.preview_photo, anchor='nw')
            self.viewer.xview_moveto(0)
            self.viewer.yview_moveto(0)
        except Exception as ex:
            self.viewer.create_text(30, 30, anchor='nw', fill=self.ink, text=f'Ошибка просмотра: {ex}')

    def clear_thumbs(self):
        self.thumb_canvas.delete('all')
        self.thumb_photos.clear()
        self.thumb_cache.clear()
        self.thumb_visible_keys = None
        self.thumb_canvas.configure(scrollregion=(0,0,208,1))

    def _thumb_scroll(self,*args):
        self.thumb_canvas.yview(*args)
        self._schedule_thumb_refresh()

    def _thumb_wheel(self,event):
        self._thumb_scroll('scroll',-int(event.delta/120)*3,'units')
        return 'break'

    def _schedule_thumb_refresh(self):
        if self.thumb_update is not None:
            self.root.after_cancel(self.thumb_update)
        self.thumb_update = self.root.after(45,self.refresh_thumbs)

    def _focus_thumb(self,index):
        if not self.pages:return
        self.thumb_canvas.configure(scrollregion=(0,0,208,((len(self.pages)+self.thumb_columns-1)//self.thumb_columns)*self.thumb_cell_h))
        row=index//self.thumb_columns
        top=row*self.thumb_cell_h
        visible_top=self.thumb_canvas.canvasy(0)
        height=max(100,self.thumb_canvas.winfo_height())
        if top < visible_top or top+self.thumb_cell_h > visible_top+height:
            total=max(1,((len(self.pages)+self.thumb_columns-1)//self.thumb_columns)*self.thumb_cell_h)
            self.thumb_canvas.yview_moveto(max(0,min(1,(top-10)/total)))

    def shift_thumbs(self, step):
        if self.pages:self.goto(max(0,min(len(self.pages)-1,self.current+step)))

    def refresh_thumbs(self):
        self.thumb_update = None
        self.thumb_canvas.delete('all')
        self.thumb_photos.clear()
        if not self.pages:return
        cell_w=max(92,self.thumb_canvas.winfo_width()//self.thumb_columns)
        row_h=self.thumb_cell_h
        total_rows=(len(self.pages)+self.thumb_columns-1)//self.thumb_columns
        self.thumb_canvas.configure(scrollregion=(0,0,cell_w*self.thumb_columns,total_rows*row_h))
        y0=max(0,self.thumb_canvas.canvasy(0))
        h=max(200,self.thumb_canvas.winfo_height())
        first_row=max(0,int(y0//row_h)-1)
        last_row=min(total_rows,int((y0+h)//row_h)+2)
        self.thumb_text.configure(text=f'Всего: {len(self.pages)} · страница {self.current+1}')
        # Only render thumbnails within the visible viewport, not the whole PDF.
        for i in range(first_row*self.thumb_columns,min(last_row*self.thumb_columns,len(self.pages))):
            ref=self.pages[i]
            x=(i%self.thumb_columns)*cell_w
            y=(i//self.thumb_columns)*row_h
            selected=i==self.current
            border=self.accent if selected else self.border_color
            bg=self.surface if selected else self.side
            self.thumb_canvas.create_rectangle(x+5,y+4,x+cell_w-5,y+row_h-5,
                     fill=bg,outline=border,width=2 if selected else 1,
                     tags=(f'pg{i}',))
            try:
                im=self.render_ref(ref,cell_w-22,row_h-38)
                photo=ImageTk.PhotoImage(im)
                self.thumb_photos.append(photo)
                self.thumb_canvas.create_image(x+cell_w//2,y+9,anchor='n',image=photo,tags=(f'pg{i}',))
            except Exception:
                self.thumb_canvas.create_text(x+cell_w//2,y+55,text='Ошибка',tags=(f'pg{i}',))
            hint=' ⚠' if self.suspect_reason(i) else ''
            self.thumb_canvas.create_text(x+cell_w//2,y+row_h-16,text=f'{i+1}{hint}',
                 font=('Segoe UI',9,'bold' if selected else 'normal'),fill=self.ink,tags=(f'pg{i}',))
            self.thumb_canvas.tag_bind(f'pg{i}','<Button-1>',lambda e,ix=i:self.goto(ix))

    def page_hint(self):
        if not self.pages:return
        reason = self.suspect_reason(self.current)
        ref = self.pages[self.current]
        w,h = self.dimensions(ref)
        self.info.set(f'Страница {self.current+1}: {round(w)} × {round(h)} pt | '
                      + (f'⚠ Подсказка: {reason}' if reason else 'Ориентация: ' + ('альбомная' if w > h else 'книжная')))

    def suspect_reason(self, i):
        if not 0 <= i < len(self.pages):return None
        ref = self.pages[i]
        key = (ref.path, ref.page, ref.rotation)
        if key in self.suspects:
            return self.suspects[key]
        w,h = self.dimensions(ref)
        return 'альбомный лист (проверьте вручную)' if w > h+1 else None

    def scan_page(self, ref):
        """Heuristic: rotated text direction (no OCR); ordinary landscape flagged separately."""
        reason = None
        try:
            p = self.ref_page(ref)
            raw = p.get_text('dict', flags=fitz.TEXTFLAGS_TEXT)
            votes = [0,0,0,0]
            # MuPDF line direction is unrotated source coordinates; account for view rotation.
            for block in raw['blocks']:
                for line in block.get('lines', []):
                    count = sum(len(span.get('text','').strip()) for span in line.get('spans',[]))
                    if count < 2: continue
                    dx,dy = line.get('dir',(1.0,0.0))
                    degrees = (math.degrees(math.atan2(dy,dx)) + ref.rotation) % 360
                    nearest = round(degrees/90) % 4
                    if abs(((degrees-nearest*90+180)%360)-180) < 20:
                        votes[nearest] += count
            if sum(votes) >= 20:
                winner = max(range(4), key=lambda i:votes[i])
                if winner != 0 and votes[winner] / sum(votes) > .65:
                    label = {1:'текст повёрнут на 90°',2:'текст вверх ногами (180°)',3:'текст повёрнут на 270°'}[winner]
                    reason = label + ' (проверьте просмотр)'
            if reason is None:
                w,h = self.dimensions(ref)
                if w > h+1:
                    reason = 'альбомный лист (может быть нормальным)'
        except Exception:
            reason = 'не удалось проверить ориентацию'
        return reason

    def start_scan(self):
        if not self.needs_doc():return
        if self.scan_task:
            self.root.after_cancel(self.scan_task)
        self.scan_cursor = 0
        self.suspects.clear()
        self.scan_info.set('Проверка ориентации: начало')
        self.scan_task = self.root.after(10, self.scan_chunk)

    def scan_chunk(self):
        self.scan_task = None
        if not self.pages:return
        end = min(self.scan_cursor+2, len(self.pages))
        for i in range(self.scan_cursor,end):
            ref = self.pages[i]
            self.suspects[(ref.path,ref.page,ref.rotation)] = self.scan_page(ref)
        self.scan_cursor = end
        flagged = sum(bool(v) for v in self.suspects.values())
        self.scan_info.set(f'Проверено {end}/{len(self.pages)} | подозрительных: {flagged} | сканы без OCR не анализируются по тексту')
        if (end % 10 == 0) or end == len(self.pages):
            self.refresh_thumbs()
            self.page_hint()
        if end < len(self.pages):
            self.scan_task = self.root.after(15, self.scan_chunk)

    def next_suspect(self):
        if not self.needs_doc(): return
        for i in range(self.current+1,len(self.pages)):
            if self.suspect_reason(i):
                self.goto(i)
                return
        messagebox.showinfo('Проверка', 'Дальше подозрительных страниц нет. Для полного анализа нажмите «Проверить ориентацию».')

    def choose_source(self):
        path = filedialog.askopenfilename(title='Выберите новый PDF или изображение',
                    filetypes=[('PDF или изображения','*.pdf *.png *.jpg *.jpeg *.bmp *.tif *.tiff'),('Все файлы','*.*')])
        if not path:return None
        path = str(Path(path).resolve())
        if self.original_path and path == str(self.original_path):
            # Valid to insert pages from original file; no self-modifying document.
            pass
        self.store.get(path)
        return path

    def choose_source_pages(self, path, count=None, default='1'):
        src = self.store.get(path)
        if src.page_count == 1 and (count is None or count == 1):
            return [0]
        if count is None:
            msg = f'В источнике {src.page_count} страниц. Какие вставить?\nПример: 1-3, 7'
        else:
            msg = f'Для замены нужно {count} страниц из {src.page_count}.\nВведите номера в нужном порядке, например: 1, 2'
        entered = simpledialog.askstring('Страницы источника', msg, initialvalue=default, parent=self.root)
        if entered is None:return None
        indices = parse_numbers(entered, src.page_count, preserve_order=True)
        if count is not None and len(indices) != count:
            raise ValueError(f'Выбрано {len(indices)} новых страниц, требуется {count}')
        return indices

    def refs_from_source(self,path,indices):
        src = self.store.get(path)
        return [PageRef(path,i,src[i].rotation) for i in indices]

    def insert_pages(self):
        if not self.needs_doc():return
        try:
            path = self.choose_source()
            if not path:return
            indices = self.choose_source_pages(path, default='1')
            if indices is None:return
            pos = simpledialog.askinteger('Вставка страниц',
                    f'Перед какой страницей вставить? 1–{len(self.pages)+1}.\n{len(self.pages)+1} = в конец',
                    initialvalue=self.current+2, minvalue=1,maxvalue=len(self.pages)+1,parent=self.root)
            if pos is None:return
            new = self.pages.copy()
            new[pos-1:pos-1] = self.refs_from_source(path, indices)
            self.commit(new,pos-1, f'Вставлено {len(indices)} страниц')
        except Exception as ex: messagebox.showerror('Вставка',str(ex))

    def move_page(self):
        if not self.needs_doc():return
        if len(self.pages)<2:return
        pos = simpledialog.askinteger('Перемещение',f'Переместить страницу {self.current+1} на позицию (1–{len(self.pages)}):',
                minvalue=1,maxvalue=len(self.pages),initialvalue=self.current+1,parent=self.root)
        if pos is None or pos-1==self.current:return
        new = self.pages.copy()
        item = new.pop(self.current)
        new.insert(pos-1,item)
        self.commit(new,pos-1,f'Страница перемещена на позицию {pos}')

    def compare(self, old_refs, new_refs):
        """Preview first replacement pair side-by-side, confirm all mapped replacements."""
        win = tk.Toplevel(self.root)
        win.title('Сравнение перед заменой')
        win.geometry('930x660')
        win.transient(self.root)
        win.grab_set()
        result = {'ok':False}
        ttk.Label(win,text=f'Будет заменено страниц: {len(old_refs)}. Сравните первую пару.',font=('Segoe UI',13,'bold')).pack(pady=10)
        frame = ttk.Frame(win)
        frame.pack(fill='both',expand=True,padx=12,pady=6)
        win._preview_images = []
        for title,ref in [('СТАРАЯ СТРАНИЦА',old_refs[0]),('НОВАЯ СТРАНИЦА',new_refs[0])]:
            col=ttk.Frame(frame)
            col.pack(side='left',fill='both',expand=True,padx=7)
            ttk.Label(col,text=title,font=('Segoe UI',11,'bold')).pack(pady=5)
            try:
                img=self.render_ref(ref,420,510)
                photo=ImageTk.PhotoImage(img)
                win._preview_images.append(photo)
                tk.Label(col,image=photo,bg='#DDE4EC').pack(expand=True)
            except Exception as ex:
                ttk.Label(col,text=str(ex)).pack()
        ttk.Label(win,text='Остальные пары заменяются по порядку выбранных номеров; исходный PDF не перезаписывается.').pack(pady=3)
        buttons=ttk.Frame(win)
        buttons.pack(pady=12)
        def accept():
            result['ok']=True
            win.destroy()
        self._button(buttons,'Подтвердить замену',accept,True).pack(side='left',padx=12)
        self._button(buttons,'Отмена',win.destroy).pack(side='left',padx=12)
        self.root.wait_window(win)
        return result['ok']

    def replace_current(self):
        if not self.needs_doc():return
        try:
            path=self.choose_source()
            if not path:return
            inds=self.choose_source_pages(path,count=1)
            if inds is None:return
            new_refs=self.refs_from_source(path,inds)
            if not self.compare([self.pages[self.current]],new_refs):return
            new=self.pages.copy()
            new[self.current]=new_refs[0]
            self.commit(new,self.current,f'Заменена страница {self.current+1}')
        except Exception as ex:messagebox.showerror('Замена',str(ex))

    def replace_many(self):
        if not self.needs_doc():return
        target_text=simpledialog.askstring('Какие страницы заменить?',
                     'Номера исходных страниц, например: 5, 96 или 10-12',parent=self.root)
        if target_text is None:return
        try:
            targets=parse_numbers(target_text,len(self.pages),preserve_order=True)
            path=self.choose_source()
            if not path:return
            source_ids=self.choose_source_pages(path,count=len(targets),
                          default=', '.join(str(i+1) for i in range(len(targets))) if len(targets)<25 else '1')
            if source_ids is None:return
            old_refs=[self.pages[i] for i in targets]
            new_refs=self.refs_from_source(path,source_ids)
            if not self.compare(old_refs,new_refs):return
            new=self.pages.copy()
            for i,ref in zip(targets,new_refs):new[i]=ref
            self.commit(new,targets[0],f'Заменено {len(targets)} страниц')
        except Exception as ex:messagebox.showerror('Замена',str(ex))

    def delete_current(self):
        if not self.needs_doc():return
        if not messagebox.askyesno('Удалить страницу',f'Удалить страницу {self.current+1}?\nОтменить можно Ctrl+Z.'):
            return
        new=self.pages.copy()
        del new[self.current]
        self.commit(new,self.current,'Страница удалена')

    def delete_many(self):
        if not self.needs_doc():return
        entered=simpledialog.askstring('Удаление страниц','Введите номера, например 5, 96, 100-110',parent=self.root)
        if entered is None:return
        try:
            ids=parse_numbers(entered,len(self.pages))
            if len(ids)>=len(self.pages):raise ValueError('Нельзя удалить все страницы')
            if not messagebox.askyesno('Удаление',f'Удалить {len(ids)} страниц? (Ctrl+Z — отмена)'):return
            removal=set(ids)
            new=[p for i,p in enumerate(self.pages) if i not in removal]
            self.commit(new,min(ids[0],len(new)-1),f'Удалено {len(ids)} страниц')
        except Exception as ex:messagebox.showerror('Удаление',str(ex))

    def crop_current(self):
        """Non-destructive crop margins in millimetres; can undo / restore."""
        if not self.needs_doc():return
        ref=self.pages[self.current]
        page=self.ref_page(ref)
        base=fitz.Rect(ref.crop) if ref.crop else page.cropbox
        dlg=tk.Toplevel(self.root)
        dlg.title('Обрезка страницы — поля в миллиметрах')
        dlg.geometry('410x315')
        dlg.transient(self.root);dlg.grab_set()
        tk.Label(dlg,text=f'Страница {self.current+1} — обрезка видимой области',font=('Segoe UI',12,'bold')).pack(pady=12)
        tk.Label(dlg,text='Укажите, сколько убрать от каждого края (мм).\nСодержимое за границами скрывается, не удаляется.',justify='center').pack()
        frm=ttk.Frame(dlg);frm.pack(pady=12)
        values={}
        for row,(label,key) in enumerate([('Слева','left'),('Сверху','top'),('Справа','right'),('Снизу','bottom')]):
            ttk.Label(frm,text=label,width=12).grid(row=row,column=0,pady=4)
            v=tk.StringVar(value='0');values[key]=v
            ttk.Entry(frm,textvariable=v,width=12).grid(row=row,column=1,pady=4)
        def apply():
            try:
                a=[float(values[k].get().replace(',','.'))*72/25.4 for k in ('left','top','right','bottom')]
                if any(x<0 for x in a):raise ValueError('Поля должны быть неотрицательными')
                box=fitz.Rect(base.x0+a[0],base.y0+a[1],base.x1-a[2],base.y1-a[3])
                if box.width<8 or box.height<8:raise ValueError('Слишком большие поля')
                updated=self.pages.copy();updated[self.current]=replace(ref,crop=tuple(box))
                self.commit(updated,self.current,'Изменена область обрезки')
                dlg.destroy()
            except Exception as ex:messagebox.showerror('Обрезка',str(ex),parent=dlg)
        ttk.Button(dlg,text='Применить обрезку',command=apply).pack(pady=6)
        ttk.Button(dlg,text='Сбросить обрезку',command=lambda:(self._reset_crop(),dlg.destroy())).pack()
        self.root.wait_window(dlg)

    def _reset_crop(self):
        ref=self.pages[self.current]
        if ref.crop is None:return
        pages=self.pages.copy();pages[self.current]=replace(ref,crop=None)
        self.commit(pages,self.current,'Обрезка страницы сброшена')

    def merge_pdfs(self):
        paths=filedialog.askopenfilenames(title='Выберите PDF для объединения (по имени файла)',filetypes=[('PDF','*.pdf')])
        if not paths:return
        paths=sorted(paths,key=lambda p:Path(p).name.casefold())
        try:
            refs=[]
            for path in paths:
                path=str(Path(path).resolve())
                doc=self.store.get(path)
                refs.extend(PageRef(path,i,doc[i].rotation) for i in range(doc.page_count))
            if self.pages:
                if not messagebox.askyesno('Объединение',f'Добавить {len(refs)} страниц в конец текущего документа?'):
                    return
                new=self.pages.copy()+refs
                self.commit(new,self.current,f'Добавлено {len(refs)} страниц из {len(paths)} PDF')
            else:
                # First document acts as autosave base; all other files are additions.
                self.load_pdf(paths[0])
                if not self.pages:return
                if len(paths)>1:
                    rest=refs[self.store.get(str(Path(paths[0]).resolve())).page_count:]
                    self.commit(self.pages.copy()+rest,0,f'Объединено {len(paths)} PDF')
            messagebox.showinfo('Объединение','Страницы добавлены. Нажмите «Сохранить» для записи единого PDF.')
        except Exception as ex:messagebox.showerror('Объединение',str(ex))

    def images_to_pdf(self):
        images=filedialog.askopenfilenames(title='Выберите JPG/PNG (порядок по имени)',
                 filetypes=[('Изображения','*.jpg *.jpeg *.png *.bmp *.tif *.tiff')])
        if not images:return
        images=sorted(images,key=lambda p:Path(p).name.casefold())
        try:
            # Each image is converted to a PDF page without downsampling.
            refs=[]
            for path in images:
                path=str(Path(path).resolve())
                source=self.store.get(path)
                refs.append(PageRef(path,0,source[0].rotation))
            if self.pages:
                pos=simpledialog.askinteger('JPG → PDF','Вставить перед страницей (последняя + 1 = в конец):',
                       minvalue=1,maxvalue=len(self.pages)+1,initialvalue=len(self.pages)+1,parent=self.root)
                if pos is None:return
                pages=self.pages.copy();pages[pos-1:pos-1]=refs
                self.commit(pages,pos-1,f'Добавлено изображений: {len(refs)}')
                messagebox.showinfo('JPG → PDF','Изображения вставлены. Для получения PDF нажмите «Сохранить».')
            else:
                output=filedialog.asksaveasfilename(title='Сохранить PDF из изображений',defaultextension='.pdf',
                          initialfile='Изображения.pdf',filetypes=[('PDF','*.pdf')])
                if not output:return
                if str(Path(output).resolve()) in [r.path for r in refs]:
                    raise ValueError('Выходной путь совпадает с исходным')
                with fitz.open() as document:
                    for ref in refs:document.insert_pdf(self.store.get(ref.path))
                    self._atomic_save_document(document,output)
                self.load_pdf(output)
        except Exception as ex:messagebox.showerror('JPG → PDF',str(ex))

    def _atomic_save_document(self,document,output,**options):
        folder=Path(output).resolve().parent
        temp=None
        try:
            with tempfile.NamedTemporaryFile(prefix='.pdfmaster_',suffix='.pdf',dir=folder,delete=False) as f:
                temp=f.name
            document.save(temp,**options)
            with fitz.open(temp) as check:
                if check.page_count!=document.page_count:
                    raise RuntimeError('Ошибка проверки сохранённого файла')
            os.replace(temp,output)
        finally:
            if temp and os.path.isfile(temp):os.unlink(temp)

    def compress_pdf(self):
        if not self.needs_doc():return
        mode=messagebox.askyesnocancel('Сжатие PDF',
           'Выберите способ сжатия:\n\nДА — Сильное (изображения могут потерять качество).\n'
           'НЕТ — Без потери качества (только оптимизация PDF).\n'
           'ОТМЕНА — ничего не делать.')
        if mode is None:return
        output=filedialog.asksaveasfilename(title='Сохранить сжатый PDF',
                   initialfile=self.original_path.stem+'_COMPRESSED.pdf',defaultextension='.pdf',filetypes=[('PDF','*.pdf')])
        if not output:return
        forbidden={str(Path(p.path).resolve()) for p in self.pages}
        if str(Path(output).resolve()) in forbidden:
            messagebox.showerror('Безопасность','Нельзя перезаписывать исходные PDF.');return
        try:
            with self.build_output_document() as document:
                if mode:
                    if not hasattr(document,'rewrite_images'):
                        raise RuntimeError('Для сильного сжатия обновите PyMuPDF: pip install -U pymupdf')
                    document.rewrite_images(dpi_threshold=180,dpi_target=130,quality=65)
                self._atomic_save_document(document,output,garbage=4,deflate=True,
                           deflate_images=True,deflate_fonts=True,use_objstms=1)
            new_size=Path(output).stat().st_size
            messagebox.showinfo('Сжатие завершено',f'Размер результата: {new_size/1024/1024:.2f} МБ\n'
                   f'Файл: {output}\n\nСжатие не гарантирует уменьшение всех PDF.')
        except Exception as ex:messagebox.showerror('Сжатие',str(ex))

    def build_output_document(self):
        """Create final PDF from page references, preserving PDF content and crop boxes."""
        doc=fitz.open()
        try:
            n=len(self.pages);i=0
            while i<n:
                ref=self.pages[i];j=i+1
                while j<n and self.pages[j].path==ref.path and self.pages[j].page==self.pages[j-1].page+1:
                    j+=1
                doc.insert_pdf(self.store.get(ref.path),from_page=ref.page,to_page=self.pages[j-1].page,
                               links=True,annots=True,widgets=False)
                for k in range(i,j):
                    page=doc[k];item=self.pages[k]
                    if item.crop is not None:page.set_cropbox(fitz.Rect(item.crop))
                    if page.rotation!=item.rotation:page.set_rotation(item.rotation)
                i=j
            return doc
        except Exception:
            doc.close()
            raise

    def _info_window(self,title,contents):
        win=tk.Toplevel(self.root)
        win.title(f'{title} — PDF MASTER KZ')
        win.geometry('820x640')
        win.transient(self.root)
        box=tk.Frame(win,bg='#FFFFFF');box.pack(fill='both',expand=True)
        tk.Label(box,text=title,fg=self.accent_fg,bg=self.accent,font=('Segoe UI',17,'bold'),anchor='w',padx=20,pady=12).pack(fill='x')
        frame=tk.Frame(box,bg='white');frame.pack(fill='both',expand=True,padx=16,pady=14)
        scroll=tk.Scrollbar(frame)
        scroll.pack(side='right',fill='y')
        area=tk.Text(frame,wrap='word',font=('Segoe UI',11),bg='white',relief='flat',spacing1=3,
                     spacing3=6,padx=12,pady=12,yscrollcommand=scroll.set)
        area.pack(side='left',fill='both',expand=True)
        scroll.configure(command=area.yview)
        area.insert('1.0',contents);area.configure(state='disabled')
        ttk.Button(box,text='Закрыть',command=win.destroy).pack(pady=(0,12))

    def show_help(self):
        self._info_window('Руководство пользователя',f"""PDF MASTER KZ — Версия {VERSION}

1. ОТКРЫТИЕ ДОКУМЕНТА
   Нажмите «Файл → Открыть» или Ctrl+O, выберите PDF.
   Слева отображаются миниатюры ВСЕХ страниц подряд. Прокручивайте список колесом мыши.
   Миниатюры рассчитываются только для видимых страниц, чтобы не перегружать память.

2. ПРОСМОТР И НАВИГАЦИЯ
   Переключение светлой и тёмной тем доступно справа сверху.
   Кнопка «Сетка» показывает по 30 страниц для быстрого обзора,
   повторное нажатие возвращает постраничный просмотр.
   Щёлкните миниатюру или введите номер страницы в верхней строке.
   На вкладке «Вид» изменяйте масштаб. Page Up / Page Down перелистывают страницы.

3. ПОВОРОТ СТРАНИЦ
   Выберите страницу и нажмите «Влево 90°», «Вправо 90°» или «На 180°».
   Программа не преобразует текст страниц в изображения.

4. УДАЛЕНИЕ И ЗАМЕНА
   «Страницы → Удалить несколько» — номера вроде 5,96,110-115.
   «Вставка → Заменить несколько» — укажите исходные и новые номера страниц.
   Сравните старую и новую страницы перед подтверждением замены.

5. ВСТАВКА И ПЕРЕМЕЩЕНИЕ
   Вкладка «Вставка» позволяет добавлять страницы из PDF или изображений.
   Для перестановки выберите страницу и нажмите «Переместить».

6. ОБРЕЗКА
   «Инструменты → Обрезать страницу»: введите поля в миллиметрах.
   Обрезка скрывает края страницы, но не удаляет данные из PDF.
   Для конфиденциального удаления информации эта функция НЕ подходит.

7. ОБЪЕДИНЕНИЕ PDF
   «Инструменты → Объединить PDF»: выберите несколько PDF.
   Они добавятся в конец текущего документа. Нажмите «Сохранить» для записи результата.

8. ПРЕОБРАЗОВАНИЕ JPG В PDF
   «Инструменты → JPG в PDF»: выберите JPG, PNG, TIFF, BMP.
   Если открыт документ, изображения вставятся в него; иначе будет создан новый PDF.

9. СЖАТИЕ
   «Инструменты → Сжать PDF»: выберите сжатие без потери качества или сильное.
   При сильном сжатии изображения могут быть перекодированы и потерять детали.
   Результат всегда записывается в отдельный файл, не изменяя оригинал.

10. ПРОВЕРКА ОРИЕНТАЦИИ
   Вкладка «Проверка» находит альбомные и подозрительно повёрнутые страницы.
   Для сканов без текстового слоя точное распознавание наклона требует OCR.

11. ОТМЕНА И АВТОВОССТАНОВЛЕНИЕ
   Ctrl+Z отменяет действия, Ctrl+Y повторяет (до {MAX_UNDO} шагов).
   В процессе работы проект сохраняется в служебный JSON рядом с оригинальным PDF.
   Если программа завершилась неожиданно, при следующем открытии будет предложено восстановление.
   Не удаляйте и не перемещайте исходные PDF/фото до завершения проекта.

12. СОХРАНЕНИЕ
   Нажмите Ctrl+S или «Файл → Сохранить».
   Рекомендуется сохранять под новым именем — исходный файл не перезаписывается.
   После записи проверяется количество страниц.

13. ГОРЯЧИЕ КЛАВИШИ
   Ctrl+O — открыть; Ctrl+S — сохранить; Ctrl+Z — отменить; Ctrl+Y — повторить.
   Alt+Left / Alt+Right — повернуть; PageUp / PageDown — предыдущая/следующая.

ПОДДЕРЖКА: {SUPPORT_EMAIL}
""")

    def show_license(self):
        self._info_window('Условия лицензии',f"""ЛИЦЕНЗИЯ PDF MASTER KZ
Версия: {VERSION} · 2026 год
Автор и правообладатель: {AUTHOR}, {COMPANY}

ПРОГРАММА РАСПРОСТРАНЯЕТСЯ БЕСПЛАТНО ТОЛЬКО ДЛЯ ДОМАШНЕГО (ЛИЧНОГО) ИСПОЛЬЗОВАНИЯ.

РАЗРЕШАЕТСЯ:
• бесплатно устанавливать и использовать программу на личном компьютере для домашних, некоммерческих задач;
• создавать, редактировать и сохранять собственные PDF-документы;
• сохранять резервные копии установочного пакета для личных нужд.

НЕ РАЗРЕШАЕТСЯ БЕЗ ПИСЬМЕННОГО РАЗРЕШЕНИЯ ПРАВООБЛАДАТЕЛЯ:
• использовать программу в коммерческой деятельности, офисе, организации или для оказания платных услуг;
• продавать, сдавать в аренду программу или распространять её в составе платных комплектов;
• выдавать себя за автора либо удалять сведения о правообладателе.

ПРОГРАММА ПРЕДОСТАВЛЯЕТСЯ «КАК ЕСТЬ» БЕЗ ГАРАНТИИ БЕЗОШИБОЧНОЙ РАБОТЫ.
Пользователь самостоятельно отвечает за создание резервных копий обрабатываемых документов.

Для коммерческого лицензирования и вопросов обращайтесь: {SUPPORT_EMAIL}.

Сторонние библиотеки распространяются на условиях их собственных лицензий.
В частности, PyMuPDF имеет условия AGPL / коммерческого лицензирования; права автора на эту программу не отменяют лицензии зависимостей. При распространении необходимо обеспечить соблюдение соответствующих условий и предоставить требуемую информацию об открытых компонентах и исходном коде, когда это применимо.

© 2026 {AUTHOR}. {COMPANY}.
""")

    def show_about(self):
        self._info_window('О программе',f"""PDF MASTER KZ
Версия {VERSION} · 2026 год

Разработчик / автор:
{AUTHOR}
ИП «INTERHOST»

Электронная почта:
{SUPPORT_EMAIL}

Назначение: постраничный просмотр, поворот, замена, удаление, перемещение, обрезка, объединение, преобразование изображений в PDF и оптимизация PDF.

Операционная система: Windows 10 / Windows 11 (Python 3.10+)
Технологии: Python, Tkinter, PyMuPDF, Pillow

Лицензия: бесплатно для личного домашнего использования.
Коммерческое использование — только по отдельному разрешению правообладателя.

© 2026 {AUTHOR} · {COMPANY}
""")

    def save_pdf(self):
        if not self.needs_doc():return
        suggestion=self.original_path.stem+'_EDITED.pdf'
        output=filedialog.asksaveasfilename(title='Сохранить единый PDF',initialdir=str(self.original_path.parent),
                    initialfile=suggestion,defaultextension='.pdf',filetypes=[('PDF','*.pdf')])
        if not output:return
        output=str(Path(output).resolve())
        source_paths={p.path for p in self.pages}
        if output in source_paths or output == str(self.original_path):
            messagebox.showerror('Безопасность','Нельзя перезаписывать исходный PDF или файл, использованный для вставки. Выберите новое имя.')
            return
        temp_path=None
        doc=fitz.open()
        try:
            # Merge consecutive source pages as one range, reducing insert_pdf overhead.
            # Preserve the base source's PDF metadata and page sizes (without rasterization).
            n=len(self.pages)
            i=0
            while i<n:
                ref=self.pages[i]
                j=i+1
                while j<n and self.pages[j].path==ref.path and self.pages[j].page==self.pages[j-1].page+1:
                    j+=1
                source=self.store.get(ref.path)
                doc.insert_pdf(source,from_page=ref.page,to_page=self.pages[j-1].page,
                               links=True,annots=True,widgets=False)
                base=i
                for k in range(i,j):
                    desired=self.pages[k].rotation
                    p=doc[base+k-i]
                    if self.pages[k].crop is not None:
                        p.set_cropbox(fitz.Rect(self.pages[k].crop))
                    if p.rotation!=desired:p.set_rotation(desired)
                i=j
                if i%100==0 or i==n:
                    self.status.set(f'Подготовлено {i}/{n} страниц...')
                    self.root.update_idletasks()
            folder=Path(output).parent
            with tempfile.NamedTemporaryFile(prefix='.pdfmaster_',suffix='.pdf',dir=folder,delete=False) as f:
                temp_path=f.name
            # No image recompression or downsampling. Temporary file + atomic replacement.
            doc.save(temp_path,garbage=3,deflate=True)
            doc.close()
            with fitz.open(temp_path) as check:
                if check.page_count!=n:raise RuntimeError('Не совпадает число страниц результата')
            os.replace(temp_path,output)
            temp_path=None
            self.status.set(f'Сохранено {n} страниц: {output}')
            messagebox.showinfo('Готово',f'Сохранён единый PDF: {n} страниц\n\n{output}\n\nИсходный файл не изменён.')
            # Load saved document as a fresh base to avoid accumulating stale source references.
            try:
                if self.autosave_path().exists():self.autosave_path().unlink()
            except OSError:pass
            self.load_pdf(output)
        except Exception as ex:
            messagebox.showerror('Ошибка сохранения',str(ex))
            self.status.set('Ошибка сохранения — исходный PDF не затронут')
        finally:
            if not doc.is_closed:doc.close()
            if temp_path and os.path.exists(temp_path):
                try:os.unlink(temp_path)
                except OSError:pass

    def quit(self):
        if self.changed:
            answer=messagebox.askyesnocancel('Закрыть редактор',
                   'Есть несохранённые изменения.\n\nДа — сохранить проект восстановления и выйти.\n'
                   'Нет — выйти без восстановления.\nОтмена — остаться.')
            if answer is None:return
            if answer:self.write_autosave()
            else:
                try:self.autosave_path().unlink(missing_ok=True)
                except Exception:pass
        self.reset_document()
        self.root.destroy()


class OfficeLayoutEditor(Editor):
    """Faithful office-style layout, built from live widgets; PDF editing remains native."""

    def _style(self):
        super()._style()
        dark = self.theme_mode.get() == 'dark'
        self.bg = '#111B28' if dark else '#EAF3FF'
        self.side = '#182637' if dark else '#F5F9FF'
        self.ink = '#EAF3FF' if dark else '#152841'
        self.muted = '#A1B1C5' if dark else '#526A89'
        self.accent = '#22BFC9' if dark else '#0878E9'
        self.toolbar_bg = '#172333' if dark else '#F8FBFF'
        self.surface = '#203247' if dark else '#E4F0FF'
        self.viewer_bg = '#101B2A' if dark else '#DCEBFF'
        self.border_color = '#344B62' if dark else '#C6D8ED'
        self.accent_fg = '#FFFFFF'
        self.root.configure(bg=self.bg)
        style = ttk.Style(self.root)
        style.configure('TEntry', padding=5, fieldbackground=self.side, foreground=self.ink)
        style.configure('TButton', padding=(9, 6), background=self.toolbar_bg, foreground=self.ink)
        style.configure('Accent.TButton', padding=(9, 6), background=self.accent, foreground='white')

    def _nav_item(self, parent, text, symbol, command, selected=False):
        col = self.accent if selected else self.side
        fg = 'white' if selected else self.ink
        b = tk.Button(parent, text=f'  {symbol}    {text}', command=command, font=('Segoe UI', 11, 'bold' if selected else 'normal'),
                      anchor='w', bg=col, fg=fg, activebackground=self.accent,
                      activeforeground='white', bd=0, relief='flat', padx=10, pady=12,
                      cursor='hand2')
        b.pack(fill='x', padx=5, pady=3)
        return b

    def _top_action(self, parent, label, icon, action):
        box = tk.Frame(parent, bg=self.toolbar_bg, width=99, height=83)
        box.pack(side='left', padx=2, pady=3)
        box.pack_propagate(False)
        try: image = self._icon(icon, 31)
        except Exception: image = None
        b = tk.Button(box, text=label, image=image, compound='top', command=action,
                      font=('Segoe UI', 9), bg=self.toolbar_bg, fg=self.ink,
                      activebackground=self.surface, activeforeground=self.accent,
                      bd=0, relief='flat', cursor='hand2', padx=2, pady=5,
                      wraplength=91)
        b.pack(fill='both', expand=True)

    def _tool(self, parent, text, command, symbol='◯'):
        b = tk.Button(parent, text=f'  {symbol}   {text}', command=command,
                      anchor='w', font=('Segoe UI', 9), bg=self.toolbar_bg, fg=self.ink,
                      activebackground=self.surface, activeforeground=self.accent,
                      relief='flat', borderwidth=0, highlightthickness=1, highlightbackground=self.border_color,
                      padx=8, pady=7, cursor='hand2')
        b.pack(fill='x', pady=3, padx=12)
        return b

    def _show_doc_tools(self):
        self._clear_right()
        self._right_heading('ИНСТРУМЕНТЫ ДОКУМЕНТА')
        self._tool(self.right_content,'Объединить PDF',self.merge_pdfs,'⊞')
        self._tool(self.right_content,'JPG / PNG → PDF',self.images_to_pdf,'▧')
        self._tool(self.right_content,'Сжать PDF',self.compress_pdf,'⇩')
        self._tool(self.right_content,'Удалить диапазон страниц',self.delete_many,'▤')
        self._tool(self.right_content,'Заменить несколько страниц',self.replace_many,'⇄')
        self._tool(self.right_content,'Проверить ориентацию',self.start_scan,'✓')
        self._tool(self.right_content,'Справка',self.show_help,'?')
        self._tool(self.right_content,'О программе',self.show_about,'ⓘ')

    def _show_page_tools(self):
        self._clear_right()
        self._right_heading('Действия со страницей')
        for txt, fn, glyph in [
            ('Повернуть влево (−90°)',lambda:self.rotate(-90),'↶'),
            ('Повернуть вправо (+90°)',lambda:self.rotate(90),'↷'),
            ('Повернуть на 180°',lambda:self.rotate(180),'⟲'),
            ('Заменить страницу…',self.replace_current,'⇄'),
            ('Вставить страницы…',self.insert_pages,'⊕'),
            ('Дублировать страницу',self.duplicate_current,'▣'),
            ('Удалить страницу',self.delete_current,'▤')]:
            self._tool(self.right_content,txt,fn,glyph)
        self._right_heading('Параметры страницы')
        self.parameter_text = tk.StringVar(value='Откройте PDF')
        tk.Label(self.right_content, textvariable=self.parameter_text, bg=self.side,
                 fg=self.muted, font=('Segoe UI',9), justify='left', anchor='w',
                 wraplength=270).pack(fill='x',padx=17,pady=9)
        self._tool(self.right_content,'Обрезать страницу…',self.crop_current,'⌗')
        self._tool(self.right_content,'Переместить страницу…',self.move_page,'↕')
        self._tool(self.right_content,'Сравнить при замене…',self.replace_current,'▣')

    def duplicate_current(self):
        if not self.needs_doc(): return
        refs=list(self.pages)
        refs.insert(self.current+1,refs[self.current])
        self.commit(refs,self.current+1,'Дублирование страницы')

    def _right_heading(self, title):
        tk.Label(self.right_content, text=title, bg=self.side, fg=self.ink,
                 anchor='w', font=('Segoe UI',10,'bold')).pack(fill='x',padx=15,pady=(14,5))

    def _clear_right(self):
        for child in self.right_content.winfo_children(): child.destroy()
        self.parameter_text = None

    def _ui(self):
        root=self.root
        dark=self.theme_mode.get() == 'dark'
        root.title(f'PDF MASTER KZ — {VERSION}')
        root.geometry('1540x920')
        root.minsize(1100,680)
        # Windows-like sky-blue title band
        title_bg='#1B2C41' if dark else '#DDEEFF'
        head=tk.Frame(root,bg=title_bg,height=54)
        head.pack(fill='x');head.pack_propagate(False)
        tk.Label(head,text='▣',font=('Segoe UI',24,'bold'),fg='#C82331',bg=title_bg).pack(side='left',padx=(14,6))
        tk.Label(head,text='PDF MASTER KZ',font=('Segoe UI',14,'bold'),fg=self.ink,bg=title_bg).pack(side='left')
        self.document_title=tk.Label(head,text='   │   Откройте документ PDF',font=('Segoe UI',11),fg=self.ink,bg=title_bg)
        self.document_title.pack(side='left',padx=14)
        theme_label='☾  Тёмная тема' if dark else '☀  Светлая тема'
        tk.Button(head,text=theme_label,command=lambda:self.set_theme('light' if dark else 'dark'),
                  bg=self.toolbar_bg,fg=self.ink,relief='flat',bd=0,
                  font=('Segoe UI',9),padx=14,pady=7).pack(side='right',padx=15)
        # Original reference: large icons across the top with vertical separators
        toolbar=tk.Frame(root,bg=self.toolbar_bg,height=98)
        toolbar.pack(fill='x');toolbar.pack_propagate(False)
        actions=[('Открыть','open',self.open_pdf),('Сохранить','save',self.save_pdf),
                 ('Печать','copy',self.print_pdf),('Отменить','undo',self.undo),
                 ('Повторить','redo',self.redo),('Добавить','insert',self.insert_pages),
                 ('Заменить','replace',self.replace_current),('Удалить','delete',self.delete_current),
                 ('Повернуть','right',lambda:self.rotate(90)),('Переместить','move',self.move_page),
                 ('Ещё','help',self._file_menu)]
        for i,(name,ico,fn) in enumerate(actions):
            if i in (3,5,8,10):
                tk.Frame(toolbar,bg=self.border_color,width=1,height=55).pack(side='left',padx=6,pady=13)
            self._top_action(toolbar,name,ico,fn)
        tk.Frame(root,bg=self.border_color,height=1).pack(fill='x')
        # Permanent sidebar, thumbnail strip, document, page tools
        body=tk.Frame(root,bg=self.bg)
        body.pack(fill='both',expand=True)
        nav=tk.Frame(body,bg=self.side,width=205)
        nav.pack(side='left',fill='y');nav.pack_propagate(False)
        self._nav_item(nav,'Главная','⌂',lambda:self._show_page_tools(),True)
        self._nav_item(nav,'Страницы','▤',lambda:self.toggle_grid())
        self._nav_item(nav,'Объединить','♧',self.merge_pdfs)
        self._nav_item(nav,'Конвертировать','▧',self.images_to_pdf)
        self._nav_item(nav,'Сжать','⇩',self.compress_pdf)
        self._nav_item(nav,'Обрезать','⌗',self.crop_current)
        self._nav_item(nav,'Справка','ⓘ',self.show_help)
        tk.Frame(nav,bg=self.side).pack(fill='both',expand=True)
        tk.Label(nav,text='PDF MASTER KZ\nВерсия '+VERSION+'\n© ИП «INTERHOST», 2026',
                 justify='left',bg=self.side,fg=self.muted,font=('Segoe UI',9)).pack(anchor='w',padx=19,pady=18)
        tk.Frame(body,bg=self.border_color,width=1).pack(side='left',fill='y')
        thumbcol=tk.Frame(body,bg=self.side,width=223)
        thumbcol.pack(side='left',fill='y');thumbcol.pack_propagate(False)
        topthumb=tk.Frame(thumbcol,bg=self.side)
        topthumb.pack(fill='x',padx=10,pady=(15,8))
        tk.Label(topthumb,text='Страницы',font=('Segoe UI',11,'bold'),bg=self.side,fg=self.ink).pack(side='left')
        tk.Button(topthumb,text='⌕',command=self.jump_to_page_prompt,
                  font=('Segoe UI',13),bg=self.side,fg=self.ink,bd=0).pack(side='right')
        self.thumb_text=tk.Label(thumbcol,text='Откройте PDF',bg=self.side,fg=self.muted,font=('Segoe UI',9))
        self.thumb_text.pack(anchor='w',padx=11,pady=(0,6))
        thumbs=tk.Frame(thumbcol,bg=self.side)
        thumbs.pack(fill='both',expand=True)
        self.thumb_canvas=tk.Canvas(thumbs,bg=self.side,highlightthickness=0,width=190)
        self.thumb_scroll=ttk.Scrollbar(thumbs,orient='vertical',command=self._thumb_scroll)
        self.thumb_canvas.configure(yscrollcommand=self.thumb_scroll.set)
        self.thumb_canvas.bind('<Configure>',lambda e:self._schedule_thumb_refresh())
        self.thumb_canvas.bind('<MouseWheel>',self._thumb_wheel)
        self.thumb_canvas.bind('<Button-4>',lambda e:self._thumb_scroll('scroll',-3,'units'))
        self.thumb_canvas.bind('<Button-5>',lambda e:self._thumb_scroll('scroll',3,'units'))
        self.thumb_scroll.pack(side='right',fill='y')
        self.thumb_canvas.pack(fill='both',expand=True)
        self.thumb_columns=1
        self.thumb_cell_h=153
        self.thumb_inner=None
        tk.Frame(body,bg=self.border_color,width=1).pack(side='left',fill='y')
        right=tk.Frame(body,bg=self.side,width=305)
        right.pack(side='right',fill='y');right.pack_propagate(False)
        righttabs=tk.Frame(right,bg=self.side)
        righttabs.pack(fill='x',padx=8,pady=(12,4))
        tk.Button(righttabs,text='Страница',command=self._show_page_tools,bg=self.side,fg=self.accent,
                  bd=0,font=('Segoe UI',11,'bold'),pady=7).pack(side='left',fill='x',expand=True)
        tk.Button(righttabs,text='Документ',command=self._show_doc_tools,bg=self.side,fg=self.ink,
                  bd=0,font=('Segoe UI',11),pady=7).pack(side='left',fill='x',expand=True)
        tk.Frame(right,bg=self.accent,height=2).pack(fill='x',padx=10)
        rightcanvas=tk.Canvas(right,bg=self.side,highlightthickness=0)
        rightscroll=ttk.Scrollbar(right,orient='vertical',command=rightcanvas.yview)
        rightcanvas.configure(yscrollcommand=rightscroll.set)
        rightscroll.pack(side='right',fill='y')
        rightcanvas.pack(side='left',fill='both',expand=True)
        self.right_content=tk.Frame(rightcanvas,bg=self.side)
        right_window=rightcanvas.create_window((0,0),window=self.right_content,anchor='nw')
        self.right_content.bind('<Configure>',lambda e:rightcanvas.configure(scrollregion=rightcanvas.bbox('all')))
        rightcanvas.bind('<Configure>',lambda e:rightcanvas.itemconfigure(right_window,width=e.width))
        self._show_page_tools()
        tk.Frame(body,bg=self.border_color,width=1).pack(side='right',fill='y')
        center=tk.Frame(body,bg=self.viewer_bg)
        center.pack(side='left',fill='both',expand=True)
        self.viewer_frame=tk.Frame(center,bg=self.viewer_bg)
        self.viewer_frame.pack(fill='both',expand=True)
        self.viewer=tk.Canvas(self.viewer_frame,bg=self.viewer_bg,highlightthickness=0)
        vs=ttk.Scrollbar(self.viewer_frame,orient='vertical',command=self.viewer.yview)
        hs=ttk.Scrollbar(self.viewer_frame,orient='horizontal',command=self.viewer.xview)
        self.viewer.configure(yscrollcommand=vs.set,xscrollcommand=hs.set)
        vs.pack(side='right',fill='y'); hs.pack(side='bottom',fill='x')
        self.viewer.pack(side='left',fill='both',expand=True)
        self.viewer.bind('<Configure>',lambda e:self.schedule_render())
        self.viewer.bind('<MouseWheel>',lambda e:self.viewer.yview_scroll(-int(e.delta/120)*3,'units'))
        self.viewer.bind('<Button-4>',lambda e:self.viewer.yview_scroll(-3,'units'))
        self.viewer.bind('<Button-5>',lambda e:self.viewer.yview_scroll(3,'units'))
        self.grid_frame=tk.Frame(center,bg=self.bg)
        gbar=tk.Frame(self.grid_frame,bg=self.bg)
        gbar.pack(fill='x')
        self.grid_label=tk.Label(gbar,text='Сетка страниц',bg=self.bg,fg=self.ink)
        self.grid_label.pack(side='left',padx=12,pady=8)
        self._button(gbar,'Следующие 30 →',lambda:self.grid_shift(1)).pack(side='right',padx=8)
        self._button(gbar,'← Предыдущие 30',lambda:self.grid_shift(-1)).pack(side='right')
        self.grid_items=tk.Frame(self.grid_frame,bg=self.bg)
        self.grid_items.pack(expand=True,anchor='center')
        # Bottom viewer bar like screenshot
        navbottom=tk.Frame(root,bg=self.toolbar_bg,height=49)
        navbottom.pack(fill='x');navbottom.pack_propagate(False)
        inner=tk.Frame(navbottom,bg=self.toolbar_bg)
        inner.pack(side='left',padx=230)
        self._flatbutton(inner,'|◀',lambda:self.goto(0))
        self._flatbutton(inner,'◀',lambda:self.goto(self.current-1))
        self.page_entry=ttk.Entry(inner,textvariable=self.page_var,width=6,justify='center')
        self.page_entry.pack(side='left',padx=4)
        self.page_entry.bind('<Return>',lambda e:self.jump())
        self.count_label=tk.Label(inner,text='из 0',bg=self.toolbar_bg,fg=self.ink)
        self.count_label.pack(side='left',padx=3)
        self._flatbutton(inner,'▶',lambda:self.goto(self.current+1))
        self._flatbutton(inner,'▶|',lambda:self.goto(len(self.pages)-1))
        self.grid_switch=self._flatbutton(inner,'▦  Сетка',self.toggle_grid)
        zoom=tk.Frame(navbottom,bg=self.toolbar_bg)
        zoom.pack(side='right',padx=12)
        self._flatbutton(zoom,'−',lambda:self.change_zoom(-.15))
        self.zoom_label=tk.Label(zoom,text='100%',bg=self.toolbar_bg,fg=self.ink)
        self.zoom_label.pack(side='left',padx=5)
        self._flatbutton(zoom,'+',lambda:self.change_zoom(.15))
        self._flatbutton(zoom,'⛶',self.fit_page)
        self.info_label=tk.Label(navbottom,textvariable=self.info,bg=self.toolbar_bg,fg=self.muted,font=('Segoe UI',8))
        self.info_label.pack(side='right',padx=6)
        foot=tk.Frame(root,bg=self.surface,height=27)
        foot.pack(fill='x');foot.pack_propagate(False)
        tk.Label(foot,textvariable=self.status,bg=self.surface,fg=self.ink,font=('Segoe UI',9),anchor='w').pack(side='left',fill='x',expand=True,padx=12)
        tk.Label(foot,textvariable=self.scan_info,bg=self.surface,fg=self.muted,font=('Segoe UI',9)).pack(side='right',padx=12)
        root.update_idletasks()

    def print_pdf(self):
        if not self.needs_doc(): return
        messagebox.showinfo('Печать PDF','Сначала сохраните документ. Затем откройте его в браузере или Adobe Reader и нажмите Ctrl+P.')

    def jump_to_page_prompt(self):
        if not self.needs_doc(): return
        n=simpledialog.askinteger('Переход','Номер страницы:',parent=self.root,minvalue=1,maxvalue=len(self.pages),initialvalue=self.current+1)
        if n:self.goto(n-1)

    def sync_view(self):
        super().sync_view()
        if hasattr(self,'document_title'):
            name=Path(self.original_path).name if self.original_path else 'Откройте документ PDF'
            self.document_title.configure(text='   │   '+name+ (f' ({len(self.pages)} страниц)' if self.pages else ''))
        if hasattr(self,'parameter_text') and self.parameter_text is not None and self.pages:
            ref=self.pages[self.current]
            w,h=self.dimensions(ref)
            orientation='Книжная' if h>w else ('Альбомная' if w>h else 'Квадратная')
            self.parameter_text.set(f'Номер: {self.current+1}\nРазмер: {round(w*25.4/72)} × {round(h*25.4/72)} мм\nОриентация: {orientation}')


# --- Reference-matched light Fluent interface (presentation only) ---
class ExactLightEditor(OfficeLayoutEditor):
    """Reference-matched widgets; uses the original Editor PDF engine unchanged."""
    C = {
        'accent':'#0878E9','deep':'#0069D4','soft':'#C8DDF6',
        'bg':'#EAF3FF','bg2':'#D9E9FA','white':'#FFFFFF',
        'frost':'#F5F9FF','border':'#D6E4F4','control':'#B9C7D8',
        'ink':'#17202D','navy':'#152C4B','muted':'#53647A',
        'danger':'#C82323','orange':'#D98A00','success':'#128D3C'
    }
    def _style(self):
        # Fixed design prescribed by SKILL: no theme switch or dark redesign.
        self.theme_mode.set('light')
        self.bg=self.C['bg'];self.side=self.C['frost'];self.ink=self.C['ink']
        self.muted=self.C['muted'];self.accent=self.C['accent']
        self.toolbar_bg=self.C['white'];self.surface=self.C['frost']
        self.viewer_bg=self.C['bg2'];self.border_color=self.C['border']
        self.accent_fg='white';self.word_blue=self.accent
        self.root.configure(bg=self.bg)
        st=ttk.Style(self.root)
        if 'clam' in st.theme_names():st.theme_use('clam')
        st.configure('.',font=('Segoe UI',11),background=self.bg,foreground=self.ink)
        st.configure('TEntry',padding=5,fieldbackground='white',foreground=self.ink)
        st.configure('TButton',padding=(9,6),background='white',foreground=self.ink)
        st.configure('Vertical.TScrollbar',background='#B6C7DC',troughcolor='#F1F7FE',arrowcolor=self.muted)
        st.configure('Horizontal.TScrollbar',background='#B6C7DC',troughcolor='#F1F7FE')
        self.ribbon_images={}

    @staticmethod
    def _font(size=11,bold=False):return ('Segoe UI',size,'bold' if bold else 'normal')

    def _icon_canvas(self,parent,kind,size=28,color=None,bg=None):
        color=color or self.C['navy']; bg=bg or self.C['white']
        cv=tk.Canvas(parent,width=size,height=size,highlightthickness=0,bg=bg,bd=0)
        S=size/24.0
        def line(*xy, width=1.8, smooth=False):
            cv.create_line(*[v*S for v in xy],fill=color,width=width*S,capstyle='round',joinstyle='round',smooth=smooth)
        def rect(x1,y1,x2,y2,r=0,width=1.8):
            cv.create_rectangle(x1*S,y1*S,x2*S,y2*S,outline=color,width=width*S)
        def oval(x1,y1,x2,y2,width=1.8):
            cv.create_oval(x1*S,y1*S,x2*S,y2*S,outline=color,width=width*S)
        def arc(x1,y1,x2,y2,start,extent,width=1.8):
            cv.create_arc(x1*S,y1*S,x2*S,y2*S,start=start,extent=extent,style='arc',outline=color,width=width*S)
        def poly(*xy):cv.create_polygon(*[v*S for v in xy],outline=color,fill='',width=1.8*S)
        # All graphics are drawn by vector geometry, not screenshot crops or emojis.
        if kind=='pdf':
            cv.create_polygon(4*S,1*S,15*S,1*S,21*S,7*S,21*S,23*S,4*S,23*S,fill='#D92B2B',outline='#B52020')
            cv.create_polygon(15*S,1*S,15*S,7*S,21*S,7*S,fill='#FFB6B6',outline='white')
            cv.create_text(12*S,15*S,text='PDF',fill='white',font=('Segoe UI',max(7,int(size*.23)),'bold'))
        elif kind=='folder':line(2,7,2,20,22,20,22,9,11,9,9,6,2,6,2,7)
        elif kind=='save':rect(4,3,20,21);rect(7,3,17,10);rect(8,14,17,21);line(15,4,15,9)
        elif kind=='printer':rect(5,2,19,8);rect(4,11,20,19);rect(7,16,17,23);line(7,6,17,6)
        elif kind in ('undo','redo'):
            if kind=='undo':arc(7,4,23,20,300,270);line(8,3,3,8,9,12)
            else:arc(1,4,17,20,330,270);line(16,3,21,8,15,12)
        elif kind=='add':line(5,2,15,2,20,7,20,22,5,22,5,2);line(15,2,15,7,20,7);line(8,14,17,14);line(12.5,9.5,12.5,18.5)
        elif kind=='replace':arc(3,2,21,20,30,150);arc(3,2,21,20,210,150);line(3,7,3,2,8,2);line(21,15,21,20,16,20)
        elif kind=='delete':line(4,6,20,6);line(7,6,8,22,16,22,17,6);line(9,3,15,3);line(10,10,10,18);line(14,10,14,18)
        elif kind in ('rotate-left','rotate-right','rotate'):
            arc(4,4,20,20,40,285)
            if kind=='rotate-left':line(6,3,3,8,9,9)
            else:line(18,3,21,8,15,9)
        elif kind=='move':line(12,2,12,22);line(2,12,22,12);line(8,6,12,2,16,6);line(8,18,12,22,16,18);line(6,8,2,12,6,16);line(18,8,22,12,18,16)
        elif kind=='more':
            for x in (5,12,19):cv.create_oval((x-1.3)*S,10.7*S,(x+1.3)*S,13.3*S,fill=color,outline='')
        elif kind=='home':line(2,11,12,2,22,11);line(5,10,5,22,19,22,19,10);line(10,22,10,15,14,15,14,22)
        elif kind=='pages':rect(3,5,17,22);line(8,2,21,2,21,18);line(7,8,14,8)
        elif kind=='link':arc(2,7,14,19,70,220);arc(10,5,22,17,250,220);line(9,15,15,9)
        elif kind=='convert':arc(3,2,21,20,25,155);arc(3,2,21,20,205,155);line(16,2,21,5,18,9);line(8,22,3,19,6,15)
        elif kind=='compress':line(12,2,12,17);line(6,12,12,18,18,12);line(4,21,20,21)
        elif kind=='crop':line(4,2,4,18,20,18);line(2,6,18,6,18,22)
        elif kind=='help':oval(3,3,21,21);cv.create_text(12*S,12*S,text='?',font=self._font(max(9,int(size*.36)),True),fill=color)
        elif kind=='search':oval(3,3,15,15);line(14,14,22,22)
        elif kind=='duplicate':rect(4,5,16,21);line(8,2,20,2,20,18)
        elif kind=='first':line(5,4,5,20);line(19,4,8,12,19,20)
        elif kind=='last':line(19,4,19,20);line(5,4,16,12,5,20)
        elif kind=='prev':line(16,4,8,12,16,20)
        elif kind=='next':line(8,4,16,12,8,20)
        elif kind=='single':rect(5,2,19,22)
        elif kind=='double':rect(2,3,11,21);rect(13,3,22,21)
        elif kind=='grid':
            for x in (3,13):
                for y in (3,13):rect(x,y,x+8,y+8)
        elif kind=='minus':line(5,12,19,12)
        elif kind=='plus':line(5,12,19,12);line(12,5,12,19)
        elif kind=='fullscreen':line(2,9,2,2,9,2);line(15,2,22,2,22,9);line(2,15,2,22,9,22);line(15,22,22,22,22,15)
        elif kind=='check':oval(2,2,22,22);line(6,12,10,16,18,8)
        elif kind=='info':oval(2,2,22,22);line(12,10,12,18);oval(11.5,5,12.5,6)
        elif kind=='chevron':line(7,9,12,14,17,9)
        elif kind=='file':rect(5,2,19,22);line(9,7,15,7);line(9,11,16,11)
        elif kind=='180':arc(3,3,21,21,40,290);line(16,2,21,4,19,10)
        else:oval(4,4,20,20)
        return cv

    def _gradient(self,cv,width,height,top,bottom,steps=72):
        def rgb(c):return tuple(int(c[k:k+2],16) for k in (1,3,5))
        t=rgb(top);b=rgb(bottom)
        for i in range(steps):
            frac=i/(steps-1);c='#%02x%02x%02x'%tuple(int(t[j]*(1-frac)+b[j]*frac) for j in range(3))
            cv.create_rectangle(0,height*i/steps,width,height*(i+1)/steps+1,fill=c,outline='')

    def _clickable_icon(self,parent,kind,command,size=24,color=None,bg=None):
        icon=self._icon_canvas(parent,kind,size,color,bg)
        icon.configure(cursor='hand2');icon.bind('<Button-1>',lambda e:command())
        return icon

    def _nav_item(self,parent,label,kind,command,selected=False):
        bg=self.C['accent'] if selected else self.C['frost'];fg='white' if selected else self.C['navy']
        bar=tk.Frame(parent,bg=bg,height=57,cursor='hand2')
        bar.pack(fill='x',padx=(4,10),pady=(0,5));bar.pack_propagate(False)
        icon=self._icon_canvas(bar,kind,30,fg,bg);icon.pack(side='left',padx=(22,13))
        tx=tk.Label(bar,text=label,bg=bg,fg=fg,font=self._font(13,selected),anchor='w',cursor='hand2')
        tx.pack(side='left',fill='both',expand=True)
        for w in (bar,icon,tx):w.bind('<Button-1>',lambda e,fn=command:fn())
        return bar

    def _toolbar_action(self,parent,label,kind,fn,color=None):
        item=tk.Frame(parent,bg='white',height=84,cursor='hand2')
        item.pack(side='left',fill='both',expand=True);item.pack_propagate(False)
        cv=self._icon_canvas(item,kind,31,color or self.C['deep'],'white')
        cv.pack(pady=(10,4))
        tx=tk.Label(item,text=label,fg=self.C['ink'],bg='white',font=self._font(10),cursor='hand2')
        tx.pack()
        for w in (item,cv,tx):w.bind('<Button-1>',lambda e,fn=fn:fn())
        return item

    def _tool(self,parent,text,command,kind='rotate'):
        item=tk.Frame(parent,bg='white',height=39,highlightthickness=1,highlightbackground=self.C['control'])
        item.pack(fill='x',padx=16,pady=3);item.pack_propagate(False)
        color=self.C['danger'] if kind=='delete' else self.C['navy']
        ic=self._icon_canvas(item,kind,24,color,'white');ic.pack(side='left',padx=(15,12))
        label=tk.Label(item,text=text,font=self._font(10),bg='white',fg=self.C['ink'],anchor='w',cursor='hand2')
        label.pack(side='left',fill='both',expand=True)
        for w in (item,ic,label):w.bind('<Button-1>',lambda e,fn=command:fn())
        return item

    def _right_heading(self,title):
        tk.Label(self.right_content,text=title,fg=self.C['ink'],bg='white',font=self._font(12,True),anchor='w').pack(fill='x',padx=17,pady=(12,9))

    def _right_field(self,parent,label,var,editable=False):
        row=tk.Frame(parent,bg='white',height=42);row.pack(fill='x',padx=17,pady=1);row.pack_propagate(False)
        tk.Label(row,text=label,bg='white',fg=self.ink,font=self._font(10),anchor='w',width=12).pack(side='left')
        if editable:
            ent=ttk.Entry(row,textvariable=var,font=self._font(10),justify='left')
            ent.pack(side='left',fill='x',expand=True,pady=4)
            ent.bind('<Return>',lambda e:self.jump())
        else:
            tk.Label(row,textvariable=var,font=self._font(10),fg=self.ink,bg=self.C['frost'],anchor='w',padx=7,
                     relief='solid',bd=1,highlightthickness=0).pack(side='left',fill='both',expand=True,pady=4)

    def _show_page_tools(self):
        self._clear_right();self._select_right_tab('page')
        self._right_heading('Действия со страницей')
        for label,func,icon in [
          ('Повернуть влево (−90°)',lambda:self.rotate(-90),'rotate-left'),
          ('Повернуть вправо (+90°)',lambda:self.rotate(90),'rotate-right'),
          ('Повернуть на 180°',lambda:self.rotate(180),'180'),
          ('Заменить страницу...',self.replace_current,'replace'),
          ('Вставить страницы...',self.insert_pages,'add'),
          ('Дублировать страницу',self.duplicate_current,'duplicate'),
          ('Удалить страницу',self.delete_current,'delete')]:self._tool(self.right_content,label,func,icon)
        tk.Frame(self.right_content,height=1,bg=self.C['border']).pack(fill='x',padx=17,pady=(12,0))
        self._right_heading('Параметры страницы')
        self.parameter_text=tk.StringVar(value='')
        self.size_var=tk.StringVar(value='—');self.orientation_var=tk.StringVar(value='—')
        self._right_field(self.right_content,'Номер:',self.page_var,True)
        self._right_field(self.right_content,'Размер:',self.size_var)
        self._right_field(self.right_content,'Ориентация:',self.orientation_var)
        self._tool(self.right_content,'Обрезать страницу...',self.crop_current,'crop')

    def _show_doc_tools(self):
        self._clear_right();self._select_right_tab('doc')
        self._right_heading('Инструменты документа')
        for label,func,icon in [
          ('Объединить PDF',self.merge_pdfs,'link'),('JPG / PNG → PDF',self.images_to_pdf,'convert'),
          ('Сжать PDF',self.compress_pdf,'compress'),('Удалить диапазон',self.delete_many,'delete'),
          ('Заменить несколько страниц',self.replace_many,'replace'),
          ('Переместить страницу',self.move_page,'move'),('Проверить ориентацию',self.start_scan,'check'),
          ('Найти подозрительную',self.next_suspect,'search'),('Справка',self.show_help,'help'),
          ('Лицензия',self.show_license,'file'),('О программе',self.show_about,'info')]:
            self._tool(self.right_content,label,func,icon)

    def _select_right_tab(self,name):
        for which, (label,underline) in getattr(self,'_right_tabs',{}).items():
            label.configure(fg=self.C['deep'] if which==name else self.C['navy'],font=self._font(12,which==name))
            underline.configure(bg=self.C['accent'] if which==name else self.C['border'])

    def _ui(self):
        r=self.root;r.title(f'PDF MASTER KZ {VERSION}')
        r.geometry('1648x928');r.minsize(1190,720)
        # Root master grid: header 55, workspace, status 44; side spans below header.
        r.grid_rowconfigure(1,weight=1);r.grid_columnconfigure(1,weight=1)
        title=tk.Canvas(r,height=55,highlightthickness=0,bg='#E4F0FC')
        title.grid(row=0,column=0,columnspan=2,sticky='nsew')
        title.bind('<Configure>',lambda e:(title.delete('grad'),None)) # background is drawn under labels below
        title_inner=tk.Frame(title,bg='#E4F0FC',height=55);title_inner.pack(fill='both',expand=True);title_inner.pack_propagate(False)
        self._icon_canvas(title_inner,'pdf',39,bg='#E4F0FC').pack(side='left',padx=(27,11),pady=7)
        tk.Label(title_inner,text='PDF MASTER KZ',font=self._font(16,True),fg=self.C['ink'],bg='#E4F0FC').pack(side='left')
        tk.Frame(title_inner,width=1,height=27,bg='#C9D8E9').pack(side='left',padx=(24,20))
        self.document_title=tk.Label(title_inner,text='Откройте документ PDF',bg='#E4F0FC',fg=self.C['ink'],font=self._font(13))
        self.document_title.pack(side='left')
        # Caption controls are visual and bound to real window actions.
        for ch,fn in [('×',self.quit),('□',lambda:r.state('zoomed') if r.state()!='zoomed' else r.state('normal')),
                      ('—',r.iconify)]:
            tk.Button(title_inner,text=ch,command=fn,font=self._font(16),fg=self.C['navy'],bg='#E4F0FC',
                      bd=0,activebackground='#C8DDF6',width=4,cursor='hand2').pack(side='right')
        sidebar=tk.Canvas(r,width=242,highlightthickness=0,bg='#EDF5FF')
        sidebar.grid(row=1,column=0,rowspan=2,sticky='nsew')
        sidebar.grid_propagate(False)
        sidebar.bind('<Configure>',lambda e:self._draw_sidebar(sidebar,e.width,e.height))
        nav_items=tk.Frame(sidebar,bg=self.C['frost'])
        sidebar.create_window((0,44),window=nav_items,anchor='nw',width=242)
        self._nav_item(nav_items,'Главная','home',self._show_page_tools,True)
        self._nav_item(nav_items,'Страницы','pages',self.toggle_grid)
        self._nav_item(nav_items,'Объединить','link',self.merge_pdfs)
        self._nav_item(nav_items,'Конвертировать','convert',self.images_to_pdf)
        self._nav_item(nav_items,'Сжать','compress',self.compress_pdf)
        self._nav_item(nav_items,'Обрезать','crop',self.crop_current)
        self._nav_item(nav_items,'Справка','help',self.show_help)
        self.sidebar_bottom=tk.Label(sidebar,text='PDF MASTER KZ\nВерсия '+VERSION+'\n© ИП «INTERHOST», 2026',
                font=self._font(11),justify='left',fg=self.C['navy'],bg='#D9E9FA',anchor='w')
        self.sidebar_bottom_id=sidebar.create_window((30,710),window=self.sidebar_bottom,anchor='nw')
        workspace=tk.Frame(r,bg=self.bg)
        workspace.grid(row=1,column=1,sticky='nsew')
        workspace.grid_rowconfigure(1,weight=1);workspace.grid_columnconfigure(0,weight=1)
        ribbon=tk.Frame(workspace,bg='white',height=91)
        ribbon.grid(row=0,column=0,sticky='ew');ribbon.grid_propagate(False)
        actions=[('Открыть','folder',self.open_pdf,self.C['orange']),('Сохранить','save',self.save_pdf,self.C['deep']),
                 ('Печать','printer',self.print_pdf,None),('Отменить','undo',self.undo,None),
                 ('Повторить','redo',self.redo,None),('Добавить ▾','add',self.insert_pages,None),
                 ('Заменить','replace',self.replace_current,None),('Удалить','delete',self.delete_current,self.C['danger']),
                 ('Повернуть ▾','rotate',lambda:self.rotate(90),None),('Переместить','move',self.move_page,None),
                 ('Ещё','more',self._file_menu,None)]
        for i,(label,icon,fn,color) in enumerate(actions):
            if i in (3,5,8,9):tk.Frame(ribbon,bg=self.C['border'],width=1,height=55).pack(side='left',padx=1,pady=13)
            self._toolbar_action(ribbon,label,icon,fn,color)
        row=tk.Frame(workspace,bg=self.bg)
        row.grid(row=1,column=0,sticky='nsew',padx=(6,4),pady=(12,5))
        row.grid_rowconfigure(0,weight=1)
        # Left light card with lazy thumbnails
        thumbcol=tk.Frame(row,bg='white',width=248,highlightthickness=1,highlightbackground=self.C['border'])
        thumbcol.place(x=0,y=0,width=248,relheight=1);thumbcol.pack_propagate(False)
        thhead=tk.Frame(thumbcol,bg='white',height=53);thhead.pack(fill='x');thhead.pack_propagate(False)
        self.th_title=tk.Label(thhead,text='Страницы (0)',font=self._font(12,True),bg='white',fg=self.ink)
        self.th_title.pack(side='left',padx=(17,0),pady=14)
        self._clickable_icon(thhead,'search',self.jump_to_page_prompt,23,bg='white').pack(side='right',padx=15)
        tk.Frame(thumbcol,bg=self.C['border'],height=1).pack(fill='x',padx=12)
        self.thumb_text=tk.Label(thumbcol,text='',bg='white',fg=self.muted,font=self._font(8))
        # Keep this widget for inherited engine but hide to match screenshot
        thumbs=tk.Frame(thumbcol,bg='white');thumbs.pack(fill='both',expand=True,padx=(10,5),pady=(8,4))
        self.thumb_canvas=tk.Canvas(thumbs,bg='white',highlightthickness=0)
        self.thumb_scroll=ttk.Scrollbar(thumbs,orient='vertical',command=self._thumb_scroll)
        self.thumb_canvas.configure(yscrollcommand=self.thumb_scroll.set)
        self.thumb_scroll.pack(side='right',fill='y');self.thumb_canvas.pack(side='left',fill='both',expand=True)
        self.thumb_canvas.bind('<Configure>',lambda e:self._schedule_thumb_refresh())
        self.thumb_canvas.bind('<MouseWheel>',self._thumb_wheel)
        self.thumb_canvas.bind('<Button-4>',lambda e:self._thumb_scroll('scroll',-3,'units'))
        self.thumb_canvas.bind('<Button-5>',lambda e:self._thumb_scroll('scroll',3,'units'))
        self.thumb_columns=1;self.thumb_cell_h=145;self.thumb_inner=None
        center=tk.Frame(row,bg=self.bg)
        center.place(x=253,y=0,relheight=1)
        center.grid_rowconfigure(0,weight=1);center.grid_columnconfigure(0,weight=1)
        self.viewer_frame=tk.Frame(center,bg=self.bg)
        self.viewer_frame.grid(row=0,column=0,sticky='nsew')
        self.viewer=tk.Canvas(self.viewer_frame,bg=self.bg,highlightthickness=0)
        vs=ttk.Scrollbar(self.viewer_frame,orient='vertical',command=self.viewer.yview)
        hs=ttk.Scrollbar(self.viewer_frame,orient='horizontal',command=self.viewer.xview)
        self.viewer.configure(yscrollcommand=vs.set,xscrollcommand=hs.set)
        vs.pack(side='right',fill='y');hs.pack(side='bottom',fill='x');self.viewer.pack(side='left',fill='both',expand=True)
        self.viewer.bind('<Configure>',lambda e:self.schedule_render())
        self.viewer.bind('<Map>',lambda e:self.root.after(80,self._force_preview_refresh))
        self.viewer_frame.bind('<Configure>',lambda e:self.schedule_render())
        self.viewer.bind('<MouseWheel>',lambda e:self.viewer.yview_scroll(-int(e.delta/120)*3,'units'))
        self.viewer.bind('<Button-4>',lambda e:self.viewer.yview_scroll(-3,'units'))
        self.viewer.bind('<Button-5>',lambda e:self.viewer.yview_scroll(3,'units'))
        self.grid_frame=tk.Frame(center,bg=self.bg)
        self.grid_label=tk.Label(self.grid_frame,text='Сетка страниц',bg=self.bg,fg=self.ink)
        self.grid_label.pack(anchor='w')
        gbar=tk.Frame(self.grid_frame,bg=self.bg);gbar.pack(fill='x')
        self._button(gbar,'← Предыдущие 30',lambda:self.grid_shift(-1)).pack(side='left')
        self._button(gbar,'Следующие 30 →',lambda:self.grid_shift(1)).pack(side='right')
        self.grid_items=tk.Frame(self.grid_frame,bg=self.bg);self.grid_items.pack(expand=True)
        right=tk.Frame(row,bg='white',width=376,highlightthickness=1,highlightbackground=self.C['border'])
        right.place(y=0,width=376,relheight=1);right.pack_propagate(False)
        def _layout_columns(event):
            w=event.width
            left_w=248 if w>=1110 else 220
            right_w=376 if w>=1110 else 350
            thumbcol.place_configure(x=0,width=left_w)
            right.place_configure(x=max(left_w+300,w-right_w),width=right_w)
            center.place_configure(x=left_w+3,width=max(300,w-left_w-right_w-7))
        row.bind('<Configure>',_layout_columns)
        tabs=tk.Frame(right,bg='white',height=46);tabs.pack(fill='x');tabs.pack_propagate(False)
        self._right_tabs={}
        for label,name,cmd in [('Страница','page',self._show_page_tools),('Документ','doc',self._show_doc_tools)]:
            slot=tk.Frame(tabs,bg='white');slot.pack(side='left',fill='both',expand=True,padx=10)
            b=tk.Label(slot,text=label,bg='white',fg=self.ink,font=self._font(12),cursor='hand2')
            b.pack(fill='both',expand=True);b.bind('<Button-1>',lambda e,fn=cmd:fn())
            under=tk.Frame(slot,bg=self.C['border'],height=3);under.pack(fill='x')
            self._right_tabs[name]=(b,under)
        rightcanvas=tk.Canvas(right,bg='white',highlightthickness=0)
        rightscroll=ttk.Scrollbar(right,orient='vertical',command=rightcanvas.yview)
        rightcanvas.configure(yscrollcommand=rightscroll.set)
        rightscroll.pack(side='right',fill='y');rightcanvas.pack(side='left',fill='both',expand=True)
        self.right_content=tk.Frame(rightcanvas,bg='white')
        win=rightcanvas.create_window((0,0),window=self.right_content,anchor='nw')
        self.right_content.bind('<Configure>',lambda e:rightcanvas.configure(scrollregion=rightcanvas.bbox('all')))
        rightcanvas.bind('<Configure>',lambda e:rightcanvas.itemconfigure(win,width=e.width))
        self._show_page_tools()
        # Navigation float anchored below the document viewport; no extra bottom ribbon.
        navbottom=tk.Frame(center,bg='#F7FBFF',height=46,highlightthickness=1,highlightbackground=self.C['border'])
        navbottom.grid(row=1,column=0,sticky='ew',padx=0,pady=(2,0));navbottom.grid_propagate(False)
        inner=tk.Frame(navbottom,bg='#F7FBFF');inner.pack(side='left',padx=(13,0))
        def ico(parent,kind,fn,size=20,highlight=False):
            bg='#DFEEFF' if highlight else '#F7FBFF'
            holder=tk.Frame(parent,bg=bg,width=32,height=32,cursor='hand2')
            holder.pack(side='left',padx=2,pady=6);holder.pack_propagate(False)
            widget=self._clickable_icon(holder,kind,fn,size,self.C['deep'] if highlight else self.C['navy'],bg)
            widget.pack(expand=True)
            holder.bind('<Button-1>',lambda e:fn())
            return holder
        ico(inner,'first',lambda:self.goto(0));ico(inner,'prev',lambda:self.goto(self.current-1))
        self.page_entry=ttk.Entry(inner,textvariable=self.page_var,width=4,justify='center',font=self._font(10))
        self.page_entry.pack(side='left',padx=3,pady=6)
        self.page_entry.bind('<Return>',lambda e:self.jump())
        self.count_label=tk.Label(inner,text='из 0',bg='#F7FBFF',fg=self.ink,font=self._font(10))
        self.count_label.pack(side='left',padx=3)
        ico(inner,'next',lambda:self.goto(self.current+1));ico(inner,'last',lambda:self.goto(len(self.pages)-1))
        views=tk.Frame(navbottom,bg='#F7FBFF');views.pack(side='left',padx=14)
        ico(views,'single',lambda:self.toggle_grid() if self.grid_mode else None,highlight=True)
        ico(views,'double',self.toggle_grid)
        self.grid_switch=ico(views,'grid',self.toggle_grid)
        zoom=tk.Frame(navbottom,bg='#F7FBFF');zoom.pack(side='right',padx=5)
        ico(zoom,'minus',lambda:self.change_zoom(-.15))
        self.zoom_label=tk.Label(zoom,text='100%',bg='#F7FBFF',fg=self.ink,font=self._font(10),width=5)
        self.zoom_label.pack(side='left')
        ico(zoom,'plus',lambda:self.change_zoom(.15));ico(zoom,'fullscreen',self.fit_page)
        self.info_label=tk.Label(center,textvariable=self.info,bg=self.bg,fg=self.muted,font=self._font(8))
        # Footer bottom, to right of left nav
        foot=tk.Frame(r,bg='#F1F8FF',height=44,highlightthickness=1,highlightbackground=self.C['border'])
        foot.grid(row=2,column=1,sticky='nsew');foot.grid_propagate(False)
        fc=self._icon_canvas(foot,'check',23,self.C['success'],'#F1F8FF');fc.pack(side='left',padx=(24,8),pady=9)
        self.status_label=tk.Label(foot,text='Готово',bg='#F1F8FF',fg=self.ink,font=self._font(10))
        self.status_label.pack(side='left')
        self.bottom_pages=tk.Label(foot,text='Страниц: 0',bg='#F1F8FF',fg=self.ink,font=self._font(10))
        self.bottom_pages.pack(side='right',padx=(0,26))
        self.bottom_size=tk.Label(foot,text='Размер: —',bg='#F1F8FF',fg=self.ink,font=self._font(10))
        self.bottom_size.pack(side='right',padx=(0,50))
        self.scan_status=tk.Label(foot,textvariable=self.scan_info,bg='#F1F8FF',fg=self.muted,font=self._font(8))
        # keep status variable alive and visible via update
        self.status.trace_add('write',lambda *args:self._update_footer())
        r.update_idletasks()

    def _draw_sidebar(self,cv,w,h):
        cv.delete('backdrop')
        # Gradient and decorative waves are native Canvas shapes.
        n=42
        for j in range(n):
            t=j/(n-1);color='#%02x%02x%02x'%(int(241*(1-t)+216*t),int(247*(1-t)+232*t),int(254*(1-t)+250*t))
            cv.create_rectangle(0,j*h/n,w,(j+1)*h/n+2,fill=color,outline='',tags='backdrop')
        cv.create_polygon(0,h-125,42,h-145,103,h-192,179,h-218,w,h-246,w,h,0,h,
                          fill='#C9E0FC',outline='',smooth=True,tags='backdrop')
        cv.create_polygon(0,h-70,75,h-119,149,h-129,w,h-166,w,h,0,h,
                          fill='#B6D5FA',outline='',smooth=True,tags='backdrop')
        cv.tag_lower('backdrop')
        cv.coords(self.sidebar_bottom_id,30,max(550,h-104))

    def load_pdf(self, path):
        """Open with the single-page preview visible, regardless of prior view mode."""
        # The engine owns PDF loading, recovery, and file safety.
        if self.grid_mode:
            self.grid_mode = False
            self.grid_frame.grid_remove()
            self.viewer_frame.grid(row=0, column=0, sticky='nsew')
        super().load_pdf(path)
        if self.pages:
            self._force_preview_refresh()
            self.root.after(250, self._force_preview_refresh)

    def _force_preview_refresh(self):
        """Recover preview geometry after Windows DPI / layout / file changes."""
        if not self.pages or self.grid_mode or not self.viewer.winfo_exists():
            return
        if not self.viewer_frame.winfo_ismapped():
            self.viewer_frame.grid(row=0, column=0, sticky='nsew')
        self.viewer.update_idletasks()
        if self.viewer.winfo_width() >= 80 and self.viewer.winfo_height() >= 80:
            if self.render_task is not None:
                self.root.after_cancel(self.render_task)
                self.render_task = None
            self.render()
        else:
            self.schedule_render()

    def render(self):
        """Draw the actual PDF page in the central Canvas, not a screenshot.

        The previous version could draw into an uninitialised/hidden Canvas.
        Recompute the viewport after layout settles and preserve a reference to
        the Tk image so it cannot be garbage-collected.
        """
        self.render_task = None
        if self.grid_mode or not self.pages:
            return
        try:
            if not self.viewer.winfo_ismapped():
                self.root.after(120, self._force_preview_refresh)
                return
            viewport = self.viewer.winfo_width()
            height = self.viewer.winfo_height()
            if viewport < 80 or height < 80:
                self.root.after(120, self._force_preview_refresh)
                return
            ref = self.pages[self.current]
            # Match the reference page width, while staying within the viewport.
            width = max(90, min(572, viewport - 55)) * self.zoom
            image = self.render_ref(ref, width, 4500)
            if image.width < 1 or image.height < 1:
                raise RuntimeError('Пустое изображение страницы PDF')
            photo = ImageTk.PhotoImage(image, master=self.viewer)
            self.preview_photo = photo
            iw, ih = image.size
            aw = max(viewport, iw + 50)
            ah = max(height, ih + 36)
            x = max(18, (aw-iw)//2)
            y = 17
            self.viewer.delete('all')
            self.viewer.configure(scrollregion=(0, 0, aw, ah))
            self.viewer.create_rectangle(x+5, y+5, x+iw+5, y+ih+5,
                                         fill='#CBDAEB', outline='', tags=('pdf-shadow',))
            self.viewer.create_image(x, y, image=photo, anchor='nw', tags=('pdf-page',))
            self.viewer.xview_moveto(0)
            self.viewer.yview_moveto(0)
            # Keep the additional reference on the Canvas too.
            self.viewer._pdf_preview_image = photo
        except Exception as exc:
            import traceback
            details=traceback.format_exc()
            try:
                with (Path(__file__).resolve().parent / 'PDF_MASTER_KZ_preview_error.log').open('a',encoding='utf-8') as f:
                    f.write(f'Page {self.current+1}:\n{details}\n')
            except OSError:
                pass
            self.viewer.delete('all')
            self.viewer.create_text(20, 30, anchor='nw', fill='#B31B1B',
                font=('Segoe UI', 12, 'bold'), width=max(300,self.viewer.winfo_width()-45),
                text='Не удалось показать страницу PDF.\n' + str(exc) +
                '\nПодробности: PDF_MASTER_KZ_preview_error.log')
            self.status.set('Ошибка просмотра страницы: ' + str(exc))

    def refresh_thumbs(self):
        # Same lazy loading as the existing engine, but page-like thumbnails and no box outlines.
        self.thumb_update=None
        self.thumb_canvas.delete('all');self.thumb_photos.clear()
        if not self.pages:return
        w=max(110,self.thumb_canvas.winfo_width());h=max(200,self.thumb_canvas.winfo_height())
        rh=self.thumb_cell_h;total=len(self.pages)*rh
        self.thumb_canvas.configure(scrollregion=(0,0,w,total))
        y0=max(0,self.thumb_canvas.canvasy(0))
        first=max(0,int(y0//rh)-1);last=min(len(self.pages),int((y0+h)//rh)+2)
        self.th_title.configure(text=f'Страницы ({len(self.pages)})')
        for i in range(first,last):
            y=i*rh;selected=i==self.current;cx=w//2
            bg='#DDEBFF' if selected else '#FFFFFF'
            if selected:self.thumb_canvas.create_rectangle(cx-70,y+1,cx+70,y+rh-3,fill=bg,outline='',tags=(f'pg{i}',))
            ref=self.pages[i]
            try:
                img=self.render_ref(ref,100,113)
                photo=ImageTk.PhotoImage(img);self.thumb_photos.append(photo)
                iw,ih=img.size
                self.thumb_canvas.create_rectangle(cx-iw//2+2,y+9,cx+iw//2+2,y+9+ih,fill='#D5E1EF',outline='',tags=(f'pg{i}',))
                self.thumb_canvas.create_image(cx,y+6,image=photo,anchor='n',tags=(f'pg{i}',))
                self.thumb_canvas.create_rectangle(cx-iw//2,y+6,cx+iw//2,y+6+ih,
                      outline=self.C['accent'] if selected else '#C7D1DE',width=2 if selected else 1,tags=(f'pg{i}',))
            except Exception:
                self.thumb_canvas.create_text(cx,y+55,text='Ошибка',tags=(f'pg{i}',))
            hint=' ⚠' if self.suspect_reason(i) else ''
            self.thumb_canvas.create_text(cx,y+rh-13,text=f'{i+1}{hint}',font=self._font(10,selected),
                     fill=self.ink,tags=(f'pg{i}',))
            self.thumb_canvas.tag_bind(f'pg{i}','<Button-1>',lambda e,ix=i:self.goto(ix))

    def sync_view(self):
        super().sync_view()
        if self.pages:
            ref=self.pages[self.current];w,h=self.dimensions(ref)
            if getattr(self,'size_var',None) is not None:
                width_mm=round(w*25.4/72);height_mm=round(h*25.4/72)
                a4='A4 ' if sorted((width_mm,height_mm))==[210,297] else ''
                self.size_var.set(f'{a4}({width_mm} × {height_mm} мм)')
                self.orientation_var.set('Книжная' if h>w else 'Альбомная' if w>h else 'Квадратная')
            if hasattr(self,'bottom_pages'):
                self.bottom_pages.configure(text=f'Страниц: {len(self.pages)}')
                try:self.bottom_size.configure(text=f'Размер: {self.original_path.stat().st_size/1048576:.1f} МБ'.replace('.',','))
                except Exception:pass
        if hasattr(self,'document_title'):
            self.document_title.configure(text=self.original_path.name if self.original_path else 'Откройте документ PDF')

    def _update_footer(self):
        if hasattr(self,'status_label'):
            value=self.status.get()
            self.status_label.configure(text='Готово' if value.startswith(('Открыто','Сохранено','Откройте')) else value[:95])

    def toggle_grid(self):
        self.grid_mode=not self.grid_mode
        self.grid_frame.grid_forget();self.viewer_frame.grid_forget()
        if self.grid_mode:
            self.grid_frame.grid(row=0,column=0,sticky='nsew');self.show_grid()
        else:
            self.viewer_frame.grid(row=0,column=0,sticky='nsew');self.schedule_render()
        # no change to original page data or edit history

    def set_theme(self,mode):
        # Only the exact light theme is permitted by the supplied design spec.
        return


class PDFMaster52(ExactLightEditor):
    """5.2: light reference UI and independent, reversible document sessions."""
    def __init__(self, root):
        self.sessions = []
        self.active_session = -1
        self.selection = set()
        self.selection_anchor = 0
        self._thumb_drag_start = None
        self._render_serial = 0
        self._render_results = queue.Queue()
        self._render_thread = None
        self._image_cache = {}
        super().__init__(root)
        self.root.after(65, self._read_render_queue)
        self.root.bind_all('<Control-Shift-s>', lambda e: self.split_pdf(), add='+')
        self.root.bind_all('<Control-w>', lambda e: self.close_tab(), add='+')
        self.root.bind_all('<Control-a>', lambda e: self.select_all_pages(), add='+')
        self.root.bind_all('<Control-Tab>', lambda e: self.switch_tab((self.active_session+1)%len(self.sessions)) if self.sessions else None, add='+')

    def _ui(self):
        super()._ui()
        workspace=self.root.grid_slaves(row=1,column=1)[0]
        row=workspace.grid_slaves(row=1,column=0)[0]
        row.grid_configure(row=2,pady=(4,5))
        workspace.grid_rowconfigure(1,weight=0)
        workspace.grid_rowconfigure(2,weight=1)
        self.tabstrip=tk.Frame(workspace,bg='#E5F0FC',height=38)
        self.tabstrip.grid(row=1,column=0,sticky='ew')
        self.tabstrip.grid_propagate(False)
        self.tabbuttons=tk.Frame(self.tabstrip,bg='#E5F0FC')
        self.tabbuttons.pack(side='left',fill='y',padx=8)
        tk.Button(self.tabstrip,text='+',font=('Segoe UI',13,'bold'),bg='#E5F0FC',fg='#0069D4',bd=0,
                  command=self.open_pdf,cursor='hand2').pack(side='left',padx=3)
        self.thumb_canvas.bind('<ButtonPress-1>',self._thumb_press,add='+')
        self.thumb_canvas.bind('<B1-Motion>',self._thumb_motion,add='+')
        self.thumb_canvas.bind('<ButtonRelease-1>',self._thumb_release,add='+')
        self._refresh_tab_buttons()

    def _refresh_tab_buttons(self):
        if not hasattr(self,'tabbuttons'):return
        for child in self.tabbuttons.winfo_children():child.destroy()
        for i,s in enumerate(self.sessions):
            active=i==self.active_session
            bg='#FFFFFF' if active else '#DCEBFA'
            label=(s['path'].name if s['path'] else 'Документ')
            if len(label)>25:label=label[:22]+'…'
            tab=tk.Frame(self.tabbuttons,bg=bg,highlightthickness=1,highlightbackground='#C4DAF2')
            tab.pack(side='left',padx=(0,4),pady=(5,0))
            title=tk.Label(tab,text=label+(' ●' if s.get('changed') else ''),bg=bg,
                           fg='#0069D4' if active else '#34465D',font=('Segoe UI',10,'bold' if active else 'normal'),padx=9,pady=4,cursor='hand2')
            title.pack(side='left');title.bind('<Button-1>',lambda e,k=i:self.switch_tab(k))
            tk.Button(tab,text='×',bg=bg,fg='#66788E',bd=0,command=lambda k=i:self.close_tab(k),cursor='hand2').pack(side='left',padx=(0,4))

    def _snapshot_session(self):
        return {'path':self.original_path,'pages':self.pages.copy(),'current':self.current,
                'history':self.history.copy(),'future':self.future.copy(),'changed':self.changed,
                'zoom':self.zoom,'suspects':self.suspects.copy(),'scan_cursor':self.scan_cursor,
                'selection':set(self.selection)}

    def _park(self):
        if self.active_session<0:return
        if self.autosave_task is not None:
            self.write_autosave()
        self.stop_tasks()
        self.sessions[self.active_session]=self._snapshot_session()

    def _restore(self,s):
        self.original_path=s['path'];self.pages=s['pages'].copy();self.current=s['current']
        self.history=s['history'].copy();self.future=s['future'].copy()
        self.changed=s['changed'];self.zoom=s['zoom']
        self.suspects=s.get('suspects',{}).copy();self.scan_cursor=s.get('scan_cursor',0)
        self.selection=set(s.get('selection',set()))
        self.thumb_photos.clear();self.thumb_cache.clear();self.preview_photo=None
        self.thumb_canvas.delete('all');self.viewer.delete('all')
        self.grid_mode=False
        if self.grid_frame.winfo_manager():self.grid_frame.grid_remove()
        self.viewer_frame.grid(row=0,column=0,sticky='nsew')
        self.sync_view()
        self._force_preview_refresh()
        self.root.title(f'PDF MASTER KZ {VERSION} — {self.original_path.name}')

    def switch_tab(self,index):
        if not 0<=index<len(self.sessions) or index==self.active_session:return
        self._park();self.active_session=index
        self._restore(self.sessions[index]);self._refresh_tab_buttons()
        self.status.set('Активный документ: '+self.original_path.name)

    def close_tab(self,index=None):
        if index is None:index=self.active_session
        if not 0<=index<len(self.sessions):return
        if index==self.active_session:
            if self.changed and not messagebox.askyesno('Закрытие вкладки','Есть несохранённые изменения. Закрыть вкладку? Проект восстановления будет сохранён.'):
                return
            self._park()
        elif self.sessions[index].get('changed'):
            if not messagebox.askyesno('Закрытие вкладки','Закрыть изменённый документ? Автовосстановление уже записано.'):
                return
        self.sessions.pop(index)
        if not self.sessions:
            self.active_session=-1;self.pages=[];self.original_path=None;self.history=[];self.future=[]
            self.changed=False;self.selection.clear();self.viewer.delete('all');self.clear_thumbs()
            self.document_title.configure(text='Откройте документ PDF')
            self.bottom_pages.configure(text='Страниц: 0')
        else:
            self.active_session=-1
            self.switch_tab(min(index,len(self.sessions)-1))
        self._refresh_tab_buttons()

    def open_pdf(self):
        names=filedialog.askopenfilenames(title='Открыть PDF в новых вкладках',filetypes=[('PDF','*.pdf')])
        for name in names:self.load_pdf(name)

    def load_pdf(self,path):
        # Do not close source documents: other tabs may still reference them.
        try:
            path=str(Path(path).resolve())
            doc=self.store.get(path)
            refs=[PageRef(path,i,doc[i].rotation) for i in range(doc.page_count)]
        except Exception as ex:
            messagebox.showerror('Открытие PDF',str(ex));return
        self._park()
        self.active_session=len(self.sessions)
        self.sessions.append({'path':Path(path),'pages':refs,'current':0,'history':[],
                              'future':[],'changed':False,'zoom':1.0,'suspects':{},
                              'scan_cursor':0,'selection':set()})
        self._restore(self.sessions[self.active_session]);self._refresh_tab_buttons()
        # Recover only if the user requests; keep existing original validation.
        recovery=Path(path+'.manualrotator.autosave.json')
        if recovery.exists():
            try:
                data=json.loads(recovery.read_text(encoding='utf-8'))
                st=Path(path).stat()
                if data.get('version')==AUTOSAVE_VERSION and data.get('signature')=={'size':st.st_size,'mtime_ns':st.st_mtime_ns}:
                    if messagebox.askyesno('Восстановление','Найден проект восстановления для '+Path(path).name+'. Восстановить?'):
                        restored=[PageRef(**p) for p in data['pages']]
                        for ref in restored:
                            if not 0<=ref.page<self.store.get(ref.path).page_count:raise ValueError('Неправильная ссылка на страницу')
                        if restored:
                            self.pages=restored;self.current=max(0,min(data['current'],len(restored)-1))
                            self.changed=True;self.sessions[self.active_session]=self._snapshot_session();self.sync_view()
            except Exception as ex:messagebox.showwarning('Восстановление',str(ex))

    def commit(self,new_pages,new_current,desc):
        super().commit(new_pages,new_current,desc)
        self.selection={self.current}
        if self.active_session>=0:
            self.sessions[self.active_session]=self._snapshot_session()
            self._refresh_tab_buttons()

    def undo(self):
        super().undo();self.selection={self.current} if self.pages else set();self._refresh_tab_buttons()
    def redo(self):
        super().redo();self.selection={self.current} if self.pages else set();self._refresh_tab_buttons()

    def _thumb_press(self,e):
        if not self.pages:return
        y=self.thumb_canvas.canvasy(e.y)
        i=int(y//self.thumb_cell_h)
        if not 0<=i<len(self.pages):return
        ctrl=bool(e.state & 0x0004);shift=bool(e.state & 0x0001)
        if shift:
            self.selection=set(range(min(self.selection_anchor,i),max(self.selection_anchor,i)+1))
        elif ctrl:
            if i in self.selection:self.selection.remove(i)
            else:self.selection.add(i)
            self.selection_anchor=i
        else:
            if i not in self.selection:self.selection={i}
            self.selection_anchor=i
        self._thumb_drag_start=(i,e.x_root,e.y_root,not ctrl and not shift)
        self.goto(i)
        self.refresh_thumbs()

    def _thumb_motion(self,e):
        if not self._thumb_drag_start:return
        i,x,y,allowed=self._thumb_drag_start
        if allowed and abs(e.y_root-y)>12:
            self.thumb_canvas.config(cursor='fleur')

    def _thumb_release(self,e):
        info=self._thumb_drag_start;self._thumb_drag_start=None
        self.thumb_canvas.config(cursor='')
        if not info or not info[3] or not self.pages:return
        old,x,y,_=info
        if abs(e.y_root-y)<14:return
        drop=int(self.thumb_canvas.canvasy(e.y)//self.thumb_cell_h)
        drop=max(0,min(drop,len(self.pages)-1))
        moving=sorted(self.selection) if old in self.selection else [old]
        if drop in moving:return
        picked=[self.pages[i] for i in moving]
        remaining=[p for j,p in enumerate(self.pages) if j not in set(moving)]
        insertion=drop-sum(j<drop for j in moving)
        insertion=max(0,min(len(remaining),insertion))
        new=remaining[:insertion]+picked+remaining[insertion:]
        self.commit(new,insertion,f'Перемещено страниц: {len(picked)}')
        self.selection=set(range(insertion,insertion+len(picked)))
        self.refresh_thumbs()

    def refresh_thumbs(self):
        self.thumb_update=None
        if not hasattr(self,'thumb_canvas'):return
        self.thumb_canvas.delete('all');self.thumb_photos.clear()
        if not self.pages:return
        w=max(110,self.thumb_canvas.winfo_width());h=max(200,self.thumb_canvas.winfo_height())
        rh=self.thumb_cell_h;self.thumb_canvas.configure(scrollregion=(0,0,w,len(self.pages)*rh))
        y0=max(0,self.thumb_canvas.canvasy(0));first=max(0,int(y0//rh)-1)
        last=min(len(self.pages),int((y0+h)//rh)+2)
        self.th_title.configure(text=f'Страницы ({len(self.pages)})')
        for i in range(first,last):
            y=i*rh;selected=i==self.current;cx=w//2;multi=i in self.selection
            if selected or multi:
                self.thumb_canvas.create_rectangle(cx-70,y+1,cx+70,y+rh-3,
                    fill='#C8DDF6' if multi else '#DDEBFF',outline='',tags=(f'pg{i}',))
            ref=self.pages[i]
            try:
                key=(ref.path,ref.page,ref.rotation,str(ref.crop),100,113)
                im=self.thumb_cache.get(key)
                if im is None:
                    im=self.render_ref(ref,100,113)
                    if len(self.thumb_cache)>70:self.thumb_cache.clear()
                    self.thumb_cache[key]=im
                photo=ImageTk.PhotoImage(im,master=self.thumb_canvas)
                self.thumb_photos.append(photo);iw,ih=im.size
                self.thumb_canvas.create_image(cx,y+6,image=photo,anchor='n',tags=(f'pg{i}',))
                self.thumb_canvas.create_rectangle(cx-iw//2,y+6,cx+iw//2,y+6+ih,
                    outline=self.C['accent'] if multi or selected else '#C7D1DE',
                    width=2 if multi or selected else 1,tags=(f'pg{i}',))
            except Exception:self.thumb_canvas.create_text(cx,y+55,text='Ошибка',tags=(f'pg{i}',))
            hint=' ⚠' if self.suspect_reason(i) else ''
            self.thumb_canvas.create_text(cx,y+rh-13,text=f'{i+1}{hint}',font=self._font(10,selected or multi),
                fill=self.ink,tags=(f'pg{i}',))
            # Keep Canvas item click on the whole cell; Ctrl/Shift and dragging handled by widget.

    def schedule_render(self,event=None):
        if not hasattr(self,'viewer'):return
        if self.render_task is not None:
            try:self.root.after_cancel(self.render_task)
            except tk.TclError:pass
        self.render_task=self.root.after(90,self.render)

    def render(self):
        self.render_task=None
        if not self.pages or self.grid_mode:return
        ref=self.pages[self.current]
        if not self.viewer.winfo_ismapped():return
        w=self.viewer.winfo_width();h=self.viewer.winfo_height()
        if w<80 or h<80:return
        width=max(90,min(572,w-55))*self.zoom
        try:
            aw,ah=self.dimensions(ref)
            scale=min(width/max(aw,1),4500/max(ah,1))
        except Exception as ex:
            self.status.set('Ошибка геометрии: '+str(ex));return
        self._render_serial+=1;token=self._render_serial
        # Explicitly avoid using shared PyMuPDF Document objects inside background threads.
        # Every worker opens its own independent source PDF.
        if self._render_thread is not None and self._render_thread.is_alive():
            # Keep latest request pending; background loop catches up when worker returns.
            self._render_pending=(token,ref,scale)
            return
        self._spawn_render(token,ref,scale)

    def _spawn_render(self,token,ref,scale):
        def worker():
            try:
                if Path(ref.path).suffix.lower() in IMAGES:
                    with fitz.open(ref.path) as source:
                        data=source.convert_to_pdf()
                    document=fitz.open(stream=data,filetype='pdf')
                else: document=fitz.open(ref.path)
                with document:
                    with fitz.open() as single:
                        single.insert_pdf(document,from_page=ref.page,to_page=ref.page)
                        page=single[0]
                        if ref.crop:page.set_cropbox(fitz.Rect(ref.crop))
                        page.set_rotation(ref.rotation)
                        pix=page.get_pixmap(matrix=fitz.Matrix(scale,scale),alpha=False,colorspace=fitz.csRGB)
                        im=Image.frombytes('RGB',(pix.width,pix.height),pix.samples)
                        if ref.annotations:
                            self._preview_annotations(im,ref)
                self._render_results.put((token,im,None))
            except Exception as exc:self._render_results.put((token,None,str(exc)+'\n'+traceback.format_exc()))
        self._render_thread=threading.Thread(target=worker,daemon=True)
        self._render_thread.start()

    def _preview_annotations(self,image,ref):
        # Display overlay in pixels; export writes editable overlay into PDF itself.
        draw=ImageDraw.Draw(image)
        for item in ref.annotations:
            op=json.loads(item) if isinstance(item,str) else item
            if op['type']=='image':
                try:
                    with Image.open(op['path']) as src:
                        src=src.convert('RGBA'); src.thumbnail((image.width//2,image.height//3))
                        x=int(image.width*op.get('x',.5)-src.width/2)
                        y=int(image.height*op.get('y',.75)-src.height/2)
                        image.paste(src,(x,y),src)
                except Exception:pass
            else:
                try:
                    from PIL import ImageFont
                    fontpath='/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf'
                    if os.name=='nt':fontpath=r'C:\Windows\Fonts\arial.ttf'
                    font=ImageFont.truetype(fontpath,max(9,int(image.width*op.get('size',16)/595*1.6)))
                except Exception:font=None
                text=op['text'];cx=int(image.width*op.get('x',.5));cy=int(image.height*op.get('y',.5))
                color='#B2B2B2' if op['type']=='watermark' else '#144B83'
                draw.text((cx,cy),text,fill=color,font=font,anchor='mm')

    def _read_render_queue(self):
        try:
            while True:
                token,im,error=self._render_results.get_nowait()
                if token==self._render_serial and self.pages and not self.grid_mode:
                    if error:
                        self.viewer.delete('all')
                        self.viewer.create_text(20,25,text='Ошибка просмотра: '+error.splitlines()[0],anchor='nw',fill='#C82323')
                        try:
                            with (Path(__file__).parent/'PDF_MASTER_KZ_preview_error.log').open('a',encoding='utf-8') as f:f.write(error+'\n')
                        except OSError:pass
                    else:self._draw_preview(im)
                pending=getattr(self,'_render_pending',None)
                if pending:
                    self._render_pending=None
                    self._spawn_render(*pending)
        except queue.Empty:pass
        if self.root.winfo_exists():self.root.after(65,self._read_render_queue)

    def _draw_preview(self,image):
        photo=ImageTk.PhotoImage(image,master=self.viewer);self.preview_photo=photo
        width,height=image.size
        viewport=max(100,self.viewer.winfo_width());vh=max(100,self.viewer.winfo_height())
        aw=max(viewport,width+50);ah=max(vh,height+36)
        x=max(18,(aw-width)//2);y=17
        self.viewer.delete('all');self.viewer.configure(scrollregion=(0,0,aw,ah))
        self.viewer.create_rectangle(x+5,y+5,x+width+5,y+height+5,fill='#CBDAEB',outline='')
        self.viewer.create_image(x,y,image=photo,anchor='nw')
        self.viewer._pdf_preview_image=photo
        self.viewer.xview_moveto(0);self.viewer.yview_moveto(0)

    def split_pdf(self):
        if not self.needs_doc():return
        ranges=simpledialog.askstring('Разделение PDF','Диапазоны для отдельных файлов, например: 1-50; 51-100; 101-300\n'
            'Каждая группа после ; создаёт отдельный PDF.',parent=self.root)
        if not ranges:return
        try:
            groups=[parse_numbers(x,len(self.pages),preserve_order=True) for x in ranges.split(';') if x.strip()]
            if not groups:raise ValueError('Не заданы диапазоны')
        except Exception as ex:messagebox.showerror('Разделение',str(ex));return
        folder=filedialog.askdirectory(title='Папка для частей PDF')
        if not folder:return
        done=[]
        try:
            for k,group in enumerate(groups,1):
                temp=self.pages;self.pages=[temp[i] for i in group]
                try:
                    with self.build_output_document() as out:
                        dest=Path(folder)/(f'{self.original_path.stem}_part_{k:03}.pdf')
                        if dest.resolve() in {Path(p.path).resolve() for p in temp}:raise ValueError('Нельзя заменять исходник')
                        self._atomic_save_document(out,str(dest),garbage=3,deflate=True)
                    done.append(str(dest))
                finally:self.pages=temp
            messagebox.showinfo('Разделение',f'Создано файлов: {len(done)}')
            self.status.set(f'Разделено на {len(done)} PDF')
        except Exception as ex:messagebox.showerror('Разделение',str(ex))

    def find_problem_pages(self):
        if not self.needs_doc():return
        win=tk.Toplevel(self.root);win.title('Анализ пустых и повторяющихся страниц')
        win.geometry('650x520');win.configure(bg='#F5F9FF')
        tk.Label(win,text='Поиск пустых страниц и дубликатов',bg='#F5F9FF',fg='#17202D',
                 font=('Segoe UI',14,'bold')).pack(anchor='w',padx=14,pady=10)
        text=tk.Text(win,wrap='word',font=('Segoe UI',10),bg='white',fg='#17202D')
        text.pack(fill='both',expand=True,padx=14,pady=(0,10))
        def show(line):
            if win.winfo_exists():text.insert('end',line+'\n');text.see('end')
        show('Проверяются страницы. Результаты предварительные — перед удалением проверьте документ.')
        refs=self.pages.copy();stop=threading.Event()
        win.protocol('WM_DELETE_WINDOW',lambda:(stop.set(),win.destroy()))
        messages=queue.Queue()
        def worker():
            seen={};blank=[];duplicates=[];sources={}
            try:
                for idx,ref in enumerate(refs):
                    if stop.is_set():break
                    try:
                        if ref.path not in sources:
                            if Path(ref.path).suffix.lower() in IMAGES:
                                with fitz.open(ref.path) as src:data=src.convert_to_pdf()
                                sources[ref.path]=fitz.open(stream=data,filetype='pdf')
                            else:sources[ref.path]=fitz.open(ref.path)
                        page=sources[ref.path][ref.page]
                        # The page content is inspected independently of editor UI state.
                        pix=page.get_pixmap(colorspace=fitz.csGRAY,matrix=fitz.Matrix(.3,.3),alpha=False)
                        samples=pix.samples
                        dark=sum(v<230 for v in samples)
                        if dark<max(8,int(len(samples)*.004)):blank.append(idx+1)
                        digest=hashlib.sha256(samples).hexdigest()
                        key=(pix.width,pix.height,digest)
                        if key in seen:duplicates.append((seen[key],idx+1))
                        else:seen[key]=idx+1
                    except Exception as ex:messages.put(f'Ошибка страницы {idx+1}: {ex}')
                    if (idx+1)%20==0:messages.put(f'Обработано {idx+1}/{len(refs)}')
            finally:
                for doc in sources.values():doc.close()
            messages.put(('done',blank,duplicates))
        threading.Thread(target=worker,daemon=True).start()
        def poll():
            if not win.winfo_exists():return
            try:
                while True:
                    item=messages.get_nowait()
                    if isinstance(item,tuple):
                        _,blank,duplicates=item
                        show('\nПУСТЫЕ: '+(', '.join(map(str,blank)) if blank else 'не найдены'))
                        show('ВОЗМОЖНЫЕ ДУБЛИКАТЫ: '+(', '.join(f'{a} и {b}' for a,b in duplicates) if duplicates else 'не найдены'))
                        show('Обнаружение основано на пиксельном сравнении, сходные изображения могут отличаться.')
                    else:show(item)
            except queue.Empty:pass
            win.after(180,poll)
        poll()

    def _overlay_dialog(self,mode):
        if not self.needs_doc():return
        indexes=sorted(self.selection) if self.selection else [self.current]
        if mode=='image':
            path=filedialog.askopenfilename(title='Изображение подписи (PNG с прозрачностью желательно)',
                                             filetypes=[('Изображения','*.png *.jpg *.jpeg')])
            if not path:return
            value={'type':'image','path':str(Path(path).resolve()),'x':.5,'y':.78}
        else:
            heading='Водяной знак' if mode=='watermark' else 'Штамп'
            default='КОПИЯ' if mode=='stamp' else 'PDF MASTER KZ'
            label=simpledialog.askstring(heading,'Введите текст:',initialvalue=default,parent=self.root)
            if not label:return
            value={'type':mode,'text':label,'x':.5,'y':.5 if mode=='watermark' else .84,'size':36 if mode=='watermark' else 22}
        if not messagebox.askyesno('Подтверждение',f'Применить к {len(indexes)} выбранным страницам?'):
            return
        new=self.pages.copy()
        for i in indexes:
            ref=new[i]
            new[i]=replace(ref,annotations=tuple(ref.annotations)+(json.dumps(value,ensure_ascii=False),))
        self.commit(new,self.current,f'Добавлен {"водяной знак" if mode=="watermark" else "штамп" if mode=="stamp" else "образ подписи"} на {len(indexes)} стр.')

    def build_output_document(self):
        out=super().build_output_document()
        try:
            fontpath=(r'C:\Windows\Fonts\arial.ttf' if os.name=='nt' else '/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf')
            for i,ref in enumerate(self.pages):
                if not ref.annotations:continue
                page=out[i];rect=page.rect
                for raw in ref.annotations:
                    op=json.loads(raw) if isinstance(raw,str) else raw
                    if op['type']=='image':
                        if not Path(op['path']).is_file():raise FileNotFoundError('Не найдена подпись: '+op['path'])
                        cx=rect.width*op.get('x',.5);cy=rect.height*op.get('y',.78)
                        r=fitz.Rect(cx-90,cy-35,cx+90,cy+35)&rect
                        page.insert_image(r,filename=op['path'],keep_proportion=True,overlay=True)
                    else:
                        label=op['text'];size=op.get('size',24)
                        if Path(fontpath).exists():
                            page.insert_font(fontname='pdfmasterfont',fontfile=fontpath)
                            font='pdfmasterfont'
                        else:font='helv'
                        r=fitz.Rect(rect.x0+20,rect.height*op.get('y',.5)-size,
                                    rect.x1-20,rect.height*op.get('y',.5)+size*2)
                        page.insert_textbox(r,label,fontsize=size,fontname=font,
                            color=(.72,.72,.72) if op['type']=='watermark' else (.08,.3,.52),
                            align=1,overlay=True)
            return out
        except Exception:
            out.close();raise

    def _show_doc_tools(self):
        super()._show_doc_tools()
        self._right_heading('PDF MASTER KZ 5.2')
        for label,fn,ico in [
          ('Разделить PDF...',self.split_pdf,'pages'),
          ('Найти пустые и дубли...',self.find_problem_pages,'search'),
          ('Вставить подпись...',lambda:self._overlay_dialog('image'),'add'),
          ('Добавить штамп...',lambda:self._overlay_dialog('stamp'),'file'),
          ('Водяной знак...',lambda:self._overlay_dialog('watermark'),'file')]:
            self._tool(self.right_content,label,fn,ico)

    def save_pdf(self):
        if not self.needs_doc():return
        dest=filedialog.asksaveasfilename(title='Сохранить PDF',initialdir=str(self.original_path.parent),
             initialfile=self.original_path.stem+'_EDITED.pdf',defaultextension='.pdf',filetypes=[('PDF','*.pdf')])
        if not dest:return
        dest=str(Path(dest).resolve())
        if dest in {str(Path(p.path).resolve()) for p in self.pages}:
            messagebox.showerror('Безопасность','Нельзя перезаписывать исходный PDF');return
        try:
            with self.build_output_document() as out:
                self._atomic_save_document(out,dest,garbage=3,deflate=True)
            with fitz.open(dest) as check:
                if check.page_count!=len(self.pages):raise RuntimeError('Ошибка количества страниц')
            self.changed=False
            self.sessions[self.active_session]=self._snapshot_session()
            self._refresh_tab_buttons()
            try:self.autosave_path().unlink(missing_ok=True)
            except OSError:pass
            self.status.set('Сохранено: '+dest)
            messagebox.showinfo('Готово',f'Сохранено {len(self.pages)} страниц:\n{dest}')
        except Exception as ex:messagebox.showerror('Сохранение',str(ex))

    def rotate(self,degrees):
        if not self.needs_doc():return
        chosen=sorted(self.selection) if len(self.selection)>1 else [self.current]
        new=self.pages.copy()
        for i in chosen:
            ref=new[i];new[i]=replace(ref,rotation=(ref.rotation+degrees)%360)
        self.commit(new,self.current,f'Поворот {degrees:+}°: страниц {len(chosen)}')
        self.selection=set(chosen)
        self.refresh_thumbs()

    def delete_current(self):
        if not self.needs_doc():return
        indices=sorted(self.selection) if len(self.selection)>1 else [self.current]
        if len(indices)>=len(self.pages):
            messagebox.showwarning('Удаление','Нельзя удалить все страницы PDF');return
        if not messagebox.askyesno('Удалить страницы',f'Удалить страниц: {len(indices)}?\nCtrl+Z отменит операцию.'):
            return
        removed=set(indices)
        new=[page for i,page in enumerate(self.pages) if i not in removed]
        first=max(0,min(indices[0],len(new)-1))
        self.commit(new,first,f'Удалено страниц: {len(indices)}')

    def select_all_pages(self):
        if not self.pages:return
        self.selection=set(range(len(self.pages)))
        self.refresh_thumbs()
        self.status.set(f'Выбрано страниц: {len(self.selection)}')

    def quit(self):
        if self.active_session>=0:self._park()
        dirty=[s for s in self.sessions if s.get('changed')]
        if dirty and not messagebox.askyesno('Выход',f'Есть несохранённые изменения в {len(dirty)} документах.\n'
                'Проекты восстановления записаны. Закрыть программу?'):
            return
        self.stop_tasks()
        self.store.close()
        self.root.destroy()

def main():
    root=tk.Tk()
    app=PDFMaster52(root)
    root.mainloop()

if __name__=='__main__':
    main()
