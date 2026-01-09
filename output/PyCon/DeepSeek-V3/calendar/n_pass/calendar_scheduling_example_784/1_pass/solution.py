from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes
    
    # Convert blocked times to minutes from 9:00
    judith_blocked = {
        'Monday': [(12*60, 12*60+30)],  # 12:00-12:30
        'Wednesday': [(11*60+30, 12*60)]  # 11:30-12:00
    }
    
    timothy_blocked = {
        'Monday': [
            (9*60+30, 10*60),      # 9:30-10:00
            (10*60+30, 11*60+30),  # 10:30-11:30
            (12*60+30, 14*60),     # 12:30-14:00
            (15*60+30, 17*60)      # 15:30-17:00
        ],
        'Tuesday': [
            (9*60+30, 13*60),      # 9:30-13:00
            (13*60+30, 14*60),     # 13:30-14:00
            (14*60+30, 17*60)      # 14:30-17:00
        ],
        'Wednesday': [
            (9*60, 9*60+30),       # 9:00-9:30
            (10*60+30, 11*60),     # 10:30-11:00
            (13*60+30, 14*60+30),  # 13:30-14:30
            (15*60, 15*60+30),     # 15:00-15:30
            (16*60, 16*60+30)      # 16:00-16:30
        ]
    }
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    def time_conflict(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check if meeting fits within work hours
        if start_time < work_start or end_time > work_end:
            return False
        
        # Judith's preferences: avoid Monday, Wednesday before 12:00
        if day == 'Monday':
            return False
        if day == 'Wednesday' and end_time <= 12*60:
            return False
        
        # Check Judith's blocked times
        if day in judith_blocked:
            for block_start, block_end in judith_blocked[day]:
                if not (end_time <= block_start or start_time >= block_end):
                    return False
        
        # Check Timothy's blocked times
        if day in timothy_blocked:
            for block_start, block_end in timothy_blocked[day]:
                if not (end_time <= block_start or start_time >= block_end):
                    return False
        
        return True
    
    problem.addConstraint(time_conflict, ['day', 'start_time'])
    
    # Find a solution
    solution = problem.getSolution()
    
    if solution:
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