from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Convert all schedules to minutes since midnight
    # Joan: 11:30-12:00, 14:30-15:00
    joan_busy = [(11*60+30, 12*60), (14*60+30, 15*60)]
    
    # Megan: 9:00-10:00, 14:00-14:30, 16:00-16:30
    megan_busy = [(9*60, 10*60), (14*60, 14*60+30), (16*60, 16*60+30)]
    
    # Austin: free all day
    austin_busy = []
    
    # Betty: 9:30-10:00, 11:30-12:00, 13:30-14:00, 16:00-16:30
    betty_busy = [(9*60+30, 10*60), (11*60+30, 12*60), (13*60+30, 14*60), (16*60, 16*60+30)]
    
    # Judith: 9:00-11:00, 12:00-13:00, 14:00-15:00
    judith_busy = [(9*60, 11*60), (12*60, 13*60), (14*60, 15*60)]
    
    # Terry: 9:30-10:00, 11:30-12:30, 13:00-14:00, 15:00-15:30, 16:00-17:00
    terry_busy = [(9*60+30, 10*60), (11*60+30, 12*60+30), (13*60, 14*60), (15*60, 15*60+30), (16*60, 17*60)]
    
    # Kathryn: 9:30-10:00, 10:30-11:00, 11:30-13:00, 14:00-16:00, 16:30-17:00
    kathryn_busy = [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 13*60), (14*60, 16*60), (16*60+30, 17*60)]
    
    # All participants' busy times
    all_busy = [joan_busy, megan_busy, austin_busy, betty_busy, judith_busy, terry_busy, kathryn_busy]
    
    # Define possible start times (every 15 minutes for efficiency)
    possible_starts = list(range(work_start, work_end - meeting_duration + 1, 15))
    
    problem.addVariable('start_time', possible_starts)
    
    # Constraint: meeting must not overlap with any participant's busy time
    def no_overlap(start_time):
        end_time = start_time + meeting_duration
        
        for participant_busy in all_busy:
            participant_free = True
            for busy_start, busy_end in participant_busy:
                if not (end_time <= busy_start or start_time >= busy_end):
                    participant_free = False
                    break
            if not participant_free:
                return False
        return True
    
    problem.addConstraint(no_overlap, ['start_time'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        start_time_minutes = solutions[0]['start_time']
        end_time_minutes = start_time_minutes + meeting_duration
        
        # Convert back to HH:MM format
        start_hour = start_time_minutes // 60
        start_minute = start_time_minutes % 60
        end_hour = end_time_minutes // 60
        end_minute = end_time_minutes % 60
        
        print(f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
        print("Monday")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()