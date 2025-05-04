from datetime import time

def find_available_time():
    # Define the time slots for each person
    eric_blocked = [(12, 0), (14, 0)]  # Eric is busy from 12:00-13:00 and 14:00-15:00
    henry_blocked = [(9, 30), (10, 30), (11, 30), (13, 0), (14, 30), (16, 0)]  # Henry's busy periods
    # Henry's preference: not meet after 10:00
    
    # Iterate through each possible start time
    for hour in range(9, 17):
        for minute in range(0, 60):
            # Check if the time is blocked by either person
            blocked = False
            
            # Check Eric's blocked times
            if (hour == 12 and minute >= 0 and minute < 60) or (hour == 14 and minute >= 0 and minute < 60):
                blocked = True
            # Check Henry's blocked times
            if (hour == 9 and minute >= 30) or (hour == 10 and minute >= 30) or (hour == 11 and minute >= 30) or (hour == 13 and minute >= 0) or (hour == 14 and minute >= 30) or (hour == 16 and minute >= 0):
                blocked = True
            
            # Check Henry's preference: not meet after 10:00
            if hour > 10:
                blocked = True  # This ensures we don't consider times after 10:00 for Henry's preference
                
            if not blocked:
                return f"{hour:02}:{minute:02}"
    
    # If no time found (shouldn't happen as per problem statement)
    return "09:00:10:00"

print(find_available_time())