from constraint import Problem
import re

def schedule_meeting():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all schedules to minutes since midnight
    schedules = {
        'Emily': [(10*60, 10*60+30), (16*60, 16*60+30)],
        'Mason': [],
        'Maria': [(10*60+30, 11*60), (14*60, 14*60+30)],
        'Carl': [(9*60+30, 10*60), (10*60+30, 12*60+30), (13*60+30, 14*60), (14*60+30, 15*60+30), (16*60, 17*60)],
        'David': [(9*60+30, 11*60), (11*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 15*60), (16*60, 17*60)],
        'Frank': [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60+30), (14*60+30, 17*60)]
    }
    
    # Define possible start times (every minute within work hours)
    possible_start_times = list(range(work_start, work_end - meeting_duration + 1))
    
    problem.addVariable('start_time', possible_start_times)
    
    # Add constraint: meeting should not conflict with any participant's schedule
    def no_conflict(start_time, schedules):
        end_time = start_time + meeting_duration
        for person, busy_slots in schedules.items():
            for busy_start, busy_end in busy_slots:
                if not (end_time <= busy_start or start_time >= busy_end):
                    return False
        return True
    
    problem.addConstraint(lambda start_time: no_conflict(start_time, schedules), ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        start_minutes = solution['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        print(f"Monday:{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    schedule_meeting()