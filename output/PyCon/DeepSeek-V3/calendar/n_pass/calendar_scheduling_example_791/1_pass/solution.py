from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_times = list(range(0, 481, 30))  # 9:00 to 17:00 in 30-min increments
    
    # Add variables
    problem.addVariable('day', days)
    problem.addVariable('start_time', start_times)
    
    # Define busy times for Nicole (in minutes from 9:00)
    nicole_busy = {
        'Monday': [(0, 30), (240, 270), (330, 390)],
        'Tuesday': [(0, 30), (150, 270), (330, 390)],
        'Wednesday': [(60, 120), (210, 360), (420, 480)]
    }
    
    # Define busy times for Ruth (in minutes from 9:00)
    ruth_busy = {
        'Monday': [(0, 480)],
        'Tuesday': [(0, 480)],
        'Wednesday': [(0, 90), (120, 150), (180, 210), (270, 390), (420, 450)]
    }
    
    # Ruth doesn't want to meet on Wednesday after 13:30 (270 minutes from 9:00)
    def ruth_wednesday_constraint(day, start_time):
        if day == 'Wednesday':
            return start_time <= 270  # 13:30 is 270 minutes from 9:00
        return True
    
    # Check if time slot is available for both participants
    def availability_constraint(day, start_time):
        end_time = start_time + 30
        
        # Check Nicole's availability
        for busy_start, busy_end in nicole_busy[day]:
            if start_time < busy_end and end_time > busy_start:
                return False
        
        # Check Ruth's availability
        for busy_start, busy_end in ruth_busy[day]:
            if start_time < busy_end and end_time > busy_start:
                return False
        
        # Apply Ruth's Wednesday constraint
        if not ruth_wednesday_constraint(day, start_time):
            return False
            
        return True
    
    problem.addConstraint(availability_constraint, ['day', 'start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        
        # Convert minutes to time format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format output
        time_range = f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d}"
        print(f"{day} {time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()