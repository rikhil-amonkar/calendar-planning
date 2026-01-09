from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    # Define days and time slots in 30-minute intervals from 9:00 to 17:00
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    time_slots = []
    
    # Create time slots from 9:00 to 17:00 in 30-minute intervals
    for hour in range(9, 17):
        for minute in [0, 30]:
            if hour == 16 and minute == 30:
                continue  # Last slot ends at 17:00
            start_time = f"{hour:02d}:{minute:02d}"
            end_hour = hour if minute == 0 else hour + 1
            end_minute = 30 if minute == 0 else 0
            if end_minute == 0 and end_hour < 17:
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                time_slots.append((start_time, end_time))
    
    # Add variables for day and time slot
    problem.addVariable('day', days)
    problem.addVariable('time_slot', time_slots)
    
    # Define Eugene's busy times
    eugene_busy = {
        'Monday': [('11:00', '12:00'), ('13:30', '14:00'), ('14:30', '15:00'), ('16:00', '16:30')],
        'Wednesday': [('09:00', '09:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:30', '15:00')],
        'Thursday': [('09:30', '10:00'), ('11:00', '12:30')],
        'Friday': [('10:30', '11:00'), ('12:00', '12:30'), ('13:00', '13:30')]
    }
    
    # Define Eric's busy times
    eric_busy = {
        'Monday': [('09:00', '17:00')],
        'Tuesday': [('09:00', '17:00')],
        'Wednesday': [('09:00', '11:30'), ('12:00', '14:00'), ('14:30', '16:30')],
        'Thursday': [('09:00', '17:00')],
        'Friday': [('09:00', '11:00'), ('11:30', '17:00')]
    }
    
    def is_available(day, time_slot):
        start, end = time_slot
        
        # Check Eugene's availability
        if day in eugene_busy:
            for busy_start, busy_end in eugene_busy[day]:
                if not (end <= busy_start or start >= busy_end):
                    return False
        
        # Check Eric's availability
        if day in eric_busy:
            for busy_start, busy_end in eric_busy[day]:
                if not (end <= busy_start or start >= busy_end):
                    return False
        
        # Eric prefers to avoid Wednesday
        if day == 'Wednesday':
            # Only consider Wednesday if no other options exist
            # This will be handled by solution ordering
            pass
            
        return True
    
    problem.addConstraint(is_available, ['day', 'time_slot'])
    
    # Get all solutions
    solutions = problem.getSolutions()
    
    if solutions:
        # Prefer non-Wednesday days
        non_wednesday_solutions = [s for s in solutions if s['day'] != 'Wednesday']
        if non_wednesday_solutions:
            solution = non_wednesday_solutions[0]
        else:
            solution = solutions[0]  # Fallback to Wednesday if no other option
        
        day = solution['day']
        time_slot = solution['time_slot']
        start_time, end_time = time_slot
        
        print(f"{day}:{start_time}:{end_time}")
    else:
        print("No available time slot found")

if __name__ == "__main__":
    main()