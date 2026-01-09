from constraint import Problem

def main():
    problem = Problem()
    
    # Define days and time slots (in minutes from 9:00)
    days = ['Monday', 'Tuesday', 'Wednesday']
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert blocked times to minutes from 9:00
    ronald_blocked = {
        'Monday': [(10*60+30, 11*60), (12*60, 12*60+30), (15*60+30, 16*60)],
        'Tuesday': [(9*60, 9*60+30), (12*60, 12*60+30), (15*60+30, 16*60+30)],
        'Wednesday': [(9*60+30, 10*60+30), (11*60, 12*60), (12*60+30, 13*60), (13*60+30, 14*60), (16*60+30, 17*60)]
    }
    
    amber_blocked = {
        'Monday': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60+30, 12*60), (12*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 17*60)],
        'Tuesday': [(9*60, 9*60+30), (10*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 15*60+30), (16*60+30, 17*60)],
        'Wednesday': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 13*60+30), (15*60, 15*60+30)]
    }
    
    # Add variables: day and start time (in minutes from 9:00)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(work_start, work_end - meeting_duration + 1))
    
    # Constraint: meeting must fit within work hours
    def within_work_hours(day, start_time):
        return start_time >= work_start and start_time + meeting_duration <= work_end
    
    # Constraint: meeting must not overlap with Ronald's blocked times
    def not_overlap_ronald(day, start_time):
        end_time = start_time + meeting_duration
        for block_start, block_end in ronald_blocked[day]:
            if not (end_time <= block_start or start_time >= block_end):
                return False
        return True
    
    # Constraint: meeting must not overlap with Amber's blocked times
    def not_overlap_amber(day, start_time):
        end_time = start_time + meeting_duration
        for block_start, block_end in amber_blocked[day]:
            if not (end_time <= block_start or start_time >= block_end):
                return False
        return True
    
    problem.addConstraint(within_work_hours, ['day', 'start_time'])
    problem.addConstraint(not_overlap_ronald, ['day', 'start_time'])
    problem.addConstraint(not_overlap_amber, ['day', 'start_time'])
    
    # Find the earliest solution
    solutions = problem.getSolutions()
    if not solutions:
        print("No solution found")
        return
    
    # Sort by day (Monday first) and then by start time
    day_order = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2}
    solutions.sort(key=lambda s: (day_order[s['day']], s['start_time']))
    
    earliest = solutions[0]
    day = earliest['day']
    start_minutes = earliest['start_time']
    end_minutes = start_minutes + meeting_duration
    
    # Convert minutes back to time format
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    
    print(f"{day}:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")

if __name__ == "__main__":
    main()