class Logger:
    def __init__(self, isLog=True):
        self.isLog = isLog
    
    def log(self, msg):
        if self.isLog:
            print(msg)
            