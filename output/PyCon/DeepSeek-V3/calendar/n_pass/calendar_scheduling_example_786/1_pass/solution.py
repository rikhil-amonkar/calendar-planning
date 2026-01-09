from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    # Define busy times for Amy (in minutes from 9:00)
    amy_busy = {
        'Wednesday': [(11*60, 11*60+30), (13*60+30, 14*60)]
    }
    
    # Define busy times for Pamela (in minutes from 9:00)
    pamela_busy = {
        'Monday': [(9*60, 10*60+30), (11*60, 16*60+30)],
        'Tuesday': [(9*60, 9*60+30), (10*60, 17*60)],
        'Wednesday': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 13*60+30), (14*60+30, 15*60), (16*60, 16*60+30)]
    }
    
    def time_conflict(busy_slots, day, start, duration):
        """Check if proposed time conflicts with busy slots"""
        end = start + duration
        if day in busy_slots:
            for busy_start, busy_end in busy_slots[day]:
                if not (end <= busy_start or start >= busy_end):
                    return True
        return False
    
    def constraint(day, start_time):
        # Check Amy's availability
        if time_conflict(amy_busy, day, start_time, meeting_duration):
            return False
        
        # Check Pamela's availability
        if time_conflict(pamela_busy, day, start_time, meeting_duration):
            return False
        
        # Pamela's preference: avoid Monday entirely and before 16:00 on Tue/Wed
        if day == 'Monday':
            return False
        if day in ['Tuesday', 'Wednesday'] and start_time < 16 * 60:
            return False
        
        return True
    
    problem.addConstraint(constraint, ['day', 'start_time'])
    
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
        
        print(f"{day}")
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()