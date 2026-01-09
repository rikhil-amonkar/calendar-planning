from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    days = ['Monday', 'Tuesday']
    start_min = 9 * 60  # 9:00 in minutes
    end_min = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Amanda's busy times in minutes from start of day
    amanda_busy = {
        'Monday': [
            (9*60, 10*60 + 30),    # 9:00-10:30
            (11*60, 11*60 + 30),   # 11:00-11:30
            (12*60 + 30, 13*60),   # 12:30-13:00
            (13*60 + 30, 14*60),   # 13:30-14:00
            (14*60 + 30, 15*60),   # 14:30-15:00
        ],
        'Tuesday': [
            (9*60, 9*60 + 30),     # 9:00-9:30
            (10*60, 10*60 + 30),   # 10:00-10:30
            (11*60 + 30, 12*60),   # 11:30-12:00
            (13*60 + 30, 14*60 + 30),  # 13:30-14:30
            (15*60 + 30, 16*60),   # 15:30-16:00
            (16*60 + 30, 17*60),   # 16:30-17:00
        ]
    }
    
    # Nathan's busy times in minutes from start of day
    nathan_busy = {
        'Monday': [
            (10*60, 10*60 + 30),   # 10:00-10:30
            (11*60, 11*60 + 30),   # 11:00-11:30
            (13*60 + 30, 14*60 + 30),  # 13:30-14:30
            (16*60, 16*60 + 30),   # 16:00-16:30
        ],
        'Tuesday': [
            (9*60, 10*60 + 30),    # 9:00-10:30
            (11*60, 13*60),        # 11:00-13:00
            (13*60 + 30, 14*60),   # 13:30-14:00
            (14*60 + 30, 15*60 + 30),  # 14:30-15:30
            (16*60, 16*60 + 30),   # 16:00-16:30
        ]
    }
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Constraint: Nathan cannot meet on Monday
    def nathan_monday_constraint(day, start_time):
        return day != 'Monday'
    
    # Constraint: Amanda doesn't want to meet on Tuesday after 11:00
    def amanda_tuesday_constraint(day, start_time):
        if day == 'Tuesday':
            return start_time < 11 * 60
        return True
    
    # Constraint: Meeting should not overlap with Amanda's busy times
    def amanda_busy_constraint(day, start_time):
        end_time = start_time + meeting_duration
        if day in amanda_busy:
            for busy_start, busy_end in amanda_busy[day]:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        return True
    
    # Constraint: Meeting should not overlap with Nathan's busy times
    def nathan_busy_constraint(day, start_time):
        end_time = start_time + meeting_duration
        if day in nathan_busy:
            for busy_start, busy_end in nathan_busy[day]:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        return True
    
    # Add all constraints
    problem.addConstraint(nathan_monday_constraint, ['day', 'start_time'])
    problem.addConstraint(amanda_tuesday_constraint, ['day', 'start_time'])
    problem.addConstraint(amanda_busy_constraint, ['day', 'start_time'])
    problem.addConstraint(nathan_busy_constraint, ['day', 'start_time'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        day = solution['day']
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert minutes to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}")
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()