import datetime

def find_meeting_time():
    # Define the working hours
    start_time = datetime.time(9)
    end_time = datetime.time(17)
    
    # Convert times to minutes since 9:00 for easier calculations
    def time_to_min(t):
        return t.hour * 60 + t.minute
    
    # Define each person's busy periods as sets of minutes since 9:00
    jacqueline = {
        (90, 30),  # 9:00-9:30
        (660, 30), # 11:00-11:30
        (780, 30), # 12:30-13:00
        (990, 30)  # 15:30-16:00
    }
    
    harold = {
        (600, 30), # 10:00-10:30
        (900, 30), # 13:00-13:30
        (1080, 60) # 15:00-17:00
    }
    
    arthur = {
        (90, 30),  # 9:00-9:30
        (600, 90), # 10:00-12:30
        (1380, 30), # 14:30-15:00
        (990, 30)  # 15:30-17:00
    }
    
    kelly = {
        (90, 30),  # 9:00-9:30
        (600, 60), # 10:00-11:00
        (690, 90), # 11:30-12:30
        (840, 60), # 14:00-15:00
        (990, 30)  # 15:30-16:00
    }
    
    # Convert busy times to sets for easier checking
    jacqueline = set(jaqueline for t in jacqueline for t in [t[0], t[1]])
    harold = set(harold for t in harold for t in [t[0], t[1]])
    arthur = set(arthur for t in arthur for t in [t[0], t[1]])
    kelly = set(kelly for t in kelly for t in [t[0], t[1]])
    
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
        for person in [jacqueline, harold, arthur, kelly]:
            if minute in person:
                all_free = False
                break
        if all_free:
            print(f"{start.hour}:{start.minute}:{end.hour}:{end.minute} {start.weekday()}")
            return
    
    # If no slot found (though problem says there is one)
    print("No available time found")

find_meeting_time()