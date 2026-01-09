from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    days = ['Monday', 'Tuesday']
    start_min = 9 * 60  # 9:00 in minutes
    end_min = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert blocked times to minutes from start of day
    shirley_busy = {
        'Monday': [(10*60+30, 11*60), (12*60, 12*60+30), (16*60, 16*60+30)],
        'Tuesday': [(9*60+30, 10*60)]
    }
    
    albert_busy = {
        'Monday': [(9*60, 17*60)],  # Busy all day Monday
        'Tuesday': [(9*60+30, 11*60), (11*60+30, 12*60+30), (13*60, 16*60), (16*60+30, 17*60)]
    }
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Constraint: Meeting must fit within work hours (already handled by variable range)
    
    # Constraint: Meeting must not conflict with Shirley's schedule
    def shirley_available(day, start_time):
        end_time = start_time + meeting_duration
        for busy_start, busy_end in shirley_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    # Constraint: Meeting must not conflict with Albert's schedule  
    def albert_available(day, start_time):
        end_time = start_time + meeting_duration
        for busy_start, busy_end in albert_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    # Constraint: Shirley prefers not to meet on Tuesday after 10:30
    def shirley_preference(day, start_time):
        if day == 'Tuesday' and start_time >= 10*60+30:
            return False
        return True
    
    problem.addConstraint(shirley_available, ['day', 'start_time'])
    problem.addConstraint(albert_available, ['day', 'start_time'])
    problem.addConstraint(shirley_preference, ['day', 'start_time'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()