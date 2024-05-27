from pyfiglet import figlet_format

__all__ = [
    'print_title',
    'display_conjectures',
    'get_user_input'
]

# Constants
DATA_FILE = "training-data/data.csv"
VERSION = '1.0.0'

def print_title(version=VERSION):
    print(figlet_format('TxGRAFFITI', font='slant'))
    print('Version ' + version)
    print('Copyright ' + u'\u00a9' + ' 2024 Randy Davila')
    print()
    print("TxGraffiti is an artificial intelligence that makes mathematical conjectures.")
    print()
    print()

def display_conjectures(conjectures):
    print_title(version=VERSION)
    print("The conjectures are:")
    for i, conjecture in enumerate(conjectures, start=1):
        print(f"Conjecture {i}: {conjecture} (conjecture touch number = {conjecture.touch}) \n")

def get_user_input(prompt, options):
    print(prompt)
    for i, option in enumerate(options, start=1):
        print(f"{i}: {option}")
    choice = int(input("Enter the index of your choice: ")) - 1
    print()
    return choice