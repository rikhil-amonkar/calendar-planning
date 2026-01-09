from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all times to minutes since midnight
    # Shirley: 10:30-11:00, 12:00-12:30
    shirley_busy = [(10*60+30, 11*60), (12*60, 12*60+30)]
    
    # Jacob: 9:00-9:30, 10:00-10:30, 11:00-11:30, 12:30-13:30, 14:30-15:00
    jacob_busy = [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 11*60+30), 
                  (12*60+30, 13*60+30), (14*60+30, 15*60)]
    
    # Stephen: 11:30-12:00, 12:30-13:00
    stephen_busy = [(11*60+30, 12*60), (12*60+30, 13*60)]
    
    # Margaret: 9:00-9:30, 10:30-12:30, 13:00-13:30, 15:00-15:30, 16:30-17:00
    margaret_busy = [(9*60, 9*60+30), (10*60+30, 12*60+30), (13*60, 13*60+30),
                     (15*60, 15*60+30), (16*60+30, 17*60)]
    
    # Mason: 9:00-10:00, 10:30-11:00, 11:30-12:30, 13:00-13:30, 14:00-14:30, 16:30-17:00
    mason_busy = [(9*60, 10*60), (10*60+30, 11*60), (11*60+30, 12*60+30),
                  (13*60, 13*60+30), (14*60, 14*60+30), (16*60+30, 17*60)]
    
    # Margaret's preference: not before 14:30
    margaret_pref_start = 14 * 60 + 30
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    # Add variable for meeting start time
    problem.addVariable('start_time', possible_starts)
    
    # Constraint: meeting must end before work hours end
    def ends_before_work_end(start):
        return start + meeting_duration <= work_end
    
    # Constraint: Margaret's preference (not before 14:30)
    def margaret_preference(start):
        return start >= margaret_pref_start
    
    # Constraints for each person's availability
    def is_available_shirley(start):
        end = start + meeting_duration
        for busy_start, busy_end in shirley_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    def is_available_jacob(start):
        end = start + meeting_duration
        for busy_start, busy_end in jacob_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    def is_available_stephen(start):
        end = start + meeting_duration
        for busy_start, busy_end in stephen_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    def is_available_margaret(start):
        end = start + meeting_duration
        for busy_start, busy_end in margaret_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    def is_available_mason(start):
        end = start + meeting_duration
        for busy_start, busy_end in mason_busy:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    # Add all constraints
    problem.addConstraint(ends_before_work_end, ['start_time'])
    problem.addConstraint(margaret_preference, ['start_time'])
    problem.addConstraint(is_available_shirley, ['start_time'])
    problem.addConstraint(is_available_jacob, ['start_time'])
    problem.addConstraint(is_available_stephen, ['start_time'])
    problem.addConstraint(is_available_margaret, ['start_time'])
    problem.addConstraint(is_available_mason, ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first solution
        start_time_minutes = solutions[0]['start_time']
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        # Format output
        time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday:{time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()