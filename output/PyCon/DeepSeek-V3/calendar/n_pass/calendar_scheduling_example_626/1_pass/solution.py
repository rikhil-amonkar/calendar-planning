from constraint import Problem

def main():
    problem = Problem()
    
    # Define days
    days = ['Monday', 'Tuesday']
    
    # Define time slots in 30-minute intervals from 9:00 to 17:00
    time_slots = []
    for hour in range(9, 17):
        for minute in ['00', '30']:
            time_slots.append(f"{hour:02d}:{minute}")
    
    # Add variables for day and start time
    problem.addVariable('day', days)
    problem.addVariable('start_time', time_slots)
    
    # Define Patricia's busy times
    patricia_busy = {
        'Monday': [
            ('10:00', '10:30'), ('11:30', '12:00'), ('13:00', '13:30'),
            ('14:30', '15:30'), ('16:00', '16:30')
        ],
        'Tuesday': [
            ('10:00', '10:30'), ('11:00', '12:00'), ('14:00', '16:00'),
            ('16:30', '17:00')
        ]
    }
    
    # Define Jesse's busy times
    jesse_busy = {
        'Monday': [('9:00', '17:00')],  # Entire day blocked
        'Tuesday': [
            ('11:00', '11:30'), ('12:00', '12:30'), ('13:00', '14:00'),
            ('14:30', '15:00'), ('15:30', '17:00')
        ]
    }
    
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes
    
    def is_time_available(day, start_time, duration_minutes=60):
        start_minutes = time_to_minutes(start_time)
        end_minutes = start_minutes + duration_minutes
        
        # Check if meeting ends after 17:00
        if end_minutes > 17 * 60:
            return False
        
        # Check Patricia's schedule
        for busy_start, busy_end in patricia_busy[day]:
            busy_start_min = time_to_minutes(busy_start)
            busy_end_min = time_to_minutes(busy_end)
            if not (end_minutes <= busy_start_min or start_minutes >= busy_end_min):
                return False
        
        # Check Jesse's schedule
        for busy_start, busy_end in jesse_busy[day]:
            busy_start_min = time_to_minutes(busy_start)
            busy_end_min = time_to_minutes(busy_end)
            if not (end_minutes <= busy_start_min or start_minutes >= busy_end_min):
                return False
        
        return True
    
    # Add constraint
    problem.addConstraint(is_time_available, ['day', 'start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_time = solution['start_time']
        
        # Calculate end time
        start_minutes = time_to_minutes(start_time)
        end_minutes = start_minutes + 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"{day}: {start_time}-{end_time}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()