import datetime

def find_meeting_time():
    # Define the working hours
    start_time = datetime.time(9)
    end_time = datetime.time(17)
    
    # Convert times to minutes since 9:00 for easier calculations
    def time_to_min(t):
        return t.hour * 60 + t.minute
    
    # Define each person's busy periods as sets of minutes since 9:00
    emily = {
        (600, 30),  # 10:00-10:30
        (960, 30)   # 16:00-16:30
    }
    
    mason = set()
    
    maria = {
        (690, 30),  # 10:30-11:00
        (840, 30)   # 14:00-14:30
    }
    
    carl = {
        (570, 30),  # 9:30-10:00
        (690, 90),  # 10:30-12:30
        (1050, 30), # 13:30-14:00
        (1380, 30), # 14:30-15:00
        (1800, 60)  # 16:00-17:00
    }
    
    david = {
        (570, 60),  # 9:30-11:00
        (690, 30),  # 11:30-12:00
        (780, 60),  # 12:30-13:30
        (840, 60),  # 14:00-15:00
        (1800, 60)  # 16:00-17:00
    }
    
    frank = {
        (570, 60),  # 9:30-10:30
        (690, 30),  # 11:00-11:30
        (780, 90),  # 12:30-13:30
        (1380, 150) # 14:30-17:00
    }
    
    # Convert busy times to sets for easier checking
    emily = set(emily for t in emily for t in [t[0], t[1]])
    mason = set()
    maria = set(maria for t in maria for t in [t[0], t[1]])
    carl = set(carl for t in carl for t in [t[0], t[1]])
    david = set(david for t in david for t in [t[0], t[1]])
    frank = set(frank for t in frank for t in [t[0], t[1]])
    
    # Check each possible time slot
    for minute in range(540, 1080):  # 9:00 to 16:30 in 10-minute increments
        if minute % 10 != 0:
            continue
        start = datetime.time(9, (minute // 10) % 6)
        end = start + datetime.timedelta(minutes=30)
        if end > datetime.time(17):
            continue
        
        # Check if the time slot is free for everyone
        all_free = True
        for person in [emily, mason, maria, carl, david, frank]:
            if minute in person:
                all_free = False
                break
        if all_free:
            print(f"{start.hour}:{start.minute}:{end.hour}:{end.minute} {start.weekday()}")
            return
    
    # If no slot found (though problem says there is one)
    print("No available time found")

find_meeting_time()