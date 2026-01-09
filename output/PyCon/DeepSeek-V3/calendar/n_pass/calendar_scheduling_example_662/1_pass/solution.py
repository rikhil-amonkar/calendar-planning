from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Gary's blocked times in minutes from 9:00
    gary_blocked = {
        'Monday': [(9*60+30, 10*60), (11*60, 13*60), (14*60, 14*60+30), (16*60+30, 17*60)],
        'Tuesday': [(9*60, 9*60+30), (10*60+30, 11*60), (14*60+30, 16*60)]
    }
    
    # David's blocked times in minutes from 9:00
    david_blocked = {
        'Monday': [(9*60, 9*60+30), (10*60, 13*60), (14*60+30, 16*60+30)],
        'Tuesday': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60+30), 
                   (13*60, 14*60+30), (15*60, 16*60), (16*60+30, 17*60)]
    }
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    # Constraint: meeting must fit within work hours
    def within_work_hours(day, start_time):
        return start_time >= work_start and start_time + meeting_duration <= work_end
    
    # Constraint: check if time slot is free for Gary
    def gary_available(day, start_time):
        end_time = start_time + meeting_duration
        for block_start, block_end in gary_blocked[day]:
            if not (end_time <= block_start or start_time >= block_end):
                return False
        return True
    
    # Constraint: check if time slot is free for David
    def david_available(day, start_time):
        end_time = start_time + meeting_duration
        for block_start, block_end in david_blocked[day]:
            if not (end_time <= block_start or start_time >= block_end):
                return False
        return True
    
    problem.addConstraint(within_work_hours, ['day', 'start_time'])
    problem.addConstraint(gary_available, ['day', 'start_time'])
    problem.addConstraint(david_available, ['day', 'start_time'])
    
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
        
        print(f"{day}:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()