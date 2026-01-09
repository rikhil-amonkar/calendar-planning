from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    # Define busy times for Mary and Alexis (in minutes from 9:00)
    busy_times = {
        'Mary': {
            'Tuesday': [(10*60, 10*60+30), (15*60+30, 16*60)],
            'Wednesday': [(9*60+30, 10*60), (15*60, 15*60+30)],
            'Thursday': [(9*60, 10*60), (10*60+30, 11*60+30)]
        },
        'Alexis': {
            'Monday': [(9*60, 10*60), (10*60+30, 12*60), (12*60+30, 16*60+30)],
            'Tuesday': [(9*60, 10*60), (10*60+30, 11*60+30), (12*60, 15*60+30), (16*60, 17*60)],
            'Wednesday': [(9*60, 11*60), (11*60+30, 17*60)],
            'Thursday': [(10*60, 12*60), (14*60, 14*60+30), (15*60+30, 16*60), (16*60+30, 17*60)]
        }
    }
    
    def is_available(day, start_time):
        end_time = start_time + meeting_duration
        
        # Check Mary's availability
        if day in busy_times['Mary']:
            for busy_start, busy_end in busy_times['Mary'][day]:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        # Check Alexis's availability
        if day in busy_times['Alexis']:
            for busy_start, busy_end in busy_times['Alexis'][day]:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        
        return True
    
    problem.addConstraint(is_available, ['day', 'start_time'])
    
    # Find earliest solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Sort by day index and start time to find earliest
        day_order = {day: i for i, day in enumerate(days)}
        earliest = min(solutions, key=lambda s: (day_order[s['day']], s['start_time']))
        
        day = earliest['day']
        start_minutes = earliest['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert minutes to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"{day}")
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No available time slot found")

if __name__ == "__main__":
    main()