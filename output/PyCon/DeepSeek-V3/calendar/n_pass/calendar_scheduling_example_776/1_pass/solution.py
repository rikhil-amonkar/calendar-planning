from constraint import Problem
import datetime

def main():
    problem = Problem()
    
    # Define days and time slots in minutes from 9:00 (540 minutes) to 17:00 (1020 minutes)
    days = ['Monday', 'Tuesday', 'Wednesday']
    start_min = 9 * 60  # 9:00 in minutes
    end_min = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Define busy times for Jennifer in minutes from start of day
    jennifer_busy = {
        'Monday': [(9*60, 11*60), (11*60+30, 13*60), (13*60+30, 14*60+30), (15*60, 17*60)],
        'Tuesday': [(9*60, 11*60+30), (12*60, 17*60)],
        'Wednesday': [(9*60, 11*60+30), (12*60, 12*60+30), (13*60, 14*60), (14*60+30, 16*60), (16*60+30, 17*60)]
    }
    
    # John's constraints: avoid Monday after 14:30 (14*60+30 = 870 minutes)
    # John has no meetings but wants to avoid Monday after 14:30
    
    # Add variables: day and start time (in minutes from midnight)
    problem.addVariable('day', days)
    problem.addVariable('start_time', range(start_min, end_min - meeting_duration + 1))
    
    # Constraint: Meeting must not overlap with Jennifer's busy times
    def no_overlap_jennifer(day, start_time):
        end_time = start_time + meeting_duration
        for busy_start, busy_end in jennifer_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
        return True
    
    # Constraint: John wants to avoid Monday after 14:30
    def john_constraint(day, start_time):
        if day == 'Monday':
            return start_time + meeting_duration <= 14*60 + 30  # Must end by 14:30
        return True
    
    problem.addConstraint(no_overlap_jennifer, ['day', 'start_time'])
    problem.addConstraint(john_constraint, ['day', 'start_time'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        sol = solutions[0]
        day = sol['day']
        start_minutes = sol['start_time']
        end_minutes = start_minutes + meeting_duration
        
        # Convert minutes to HH:MM format
        start_time_str = f"{start_minutes // 60:02d}:{start_minutes % 60:02d}"
        end_time_str = f"{end_minutes // 60:02d}:{end_minutes % 60:02d}"
        
        print(f"{day}:{start_time_str}:{end_time_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()