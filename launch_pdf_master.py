"""Windows-friendly crash logger for PDF MASTER KZ 5.2."""
import sys
import traceback
from pathlib import Path
from datetime import datetime

def main():
    root_dir = Path(__file__).resolve().parent
    sys.path.insert(0, str(root_dir))
    try:
        import PDF_MASTER_KZ
        PDF_MASTER_KZ.main()
        return 0
    except BaseException:
        info = traceback.format_exc()
        path = root_dir / 'PDF_MASTER_KZ_launch.log'
        try:
            with path.open('a', encoding='utf-8') as log:
                log.write(f'\n{datetime.now().isoformat()}\n{info}\n')
        except OSError:
            pass
        print(info, file=sys.stderr)
        try:
            import tkinter as tk
            from tkinter import messagebox
            root = tk.Tk()
            root.withdraw()
            messagebox.showerror('PDF MASTER KZ — ошибка запуска',
                'Не удалось запустить программу.\n\n' +
                info[-1500:] + '\n\nПолный журнал: PDF_MASTER_KZ_launch.log')
            root.destroy()
        except Exception:
            pass
        return 1

if __name__ == '__main__':
    raise SystemExit(main())
