from tkinter import *

class Counter:

    def __init__(self):
        
        self.__value = 0
        self.__main_window = Tk()

        self.__current_value = Label(self.__main_window, text=self.__value)
        self.__current_value.pack()
        
        self.__increase_button = Button(self.__main_window, text='Increase',
                                        command=self.increase)
        self.__increase_button.pack()
        self.__main_window.mainloop()

    def increase(self):
        self.__value += 1
        self.__current_value.config(text=self.__value)


def main():

    Counter()


if __name__ == "__main__":
    main()