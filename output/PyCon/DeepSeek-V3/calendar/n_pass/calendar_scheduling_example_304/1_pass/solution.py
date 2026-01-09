from constraint import Problem

def main():
    problem = Problem()
    
    # Define work hours (9:00 to 17:00) in 30-minute slots
    work_start = 9 * 2  # 9:00 in half-hour units
    work_end = 17 * 2   # 17:00 in half-hour units
    
    # Convert busy times to half-hour slots
    # Christine: 9:30-10:30, 12:00-12:30, 13:00-13:30, 14:30-15:00, 16:00-16:30
    christine_busy = [(19, 21), (24, 25), (26, 27), (29, 30), (32, 33)]
    
    # Bobby: 12:00-12:30, 14:30-15:00
    bobby_busy = [(24, 25), (29, 30)]
    
    # Elizabeth: 9:00-9:30, 11:30-13:00, 13:30-14:00, 15:00-15:30, 16:00-17:00
    elizabeth_busy = [(18, 19), (23, 26), (27, 28), (30, 31), (32, 34)]
    
    # Tyler: 9:00-11:00, 12:00-12:30, 13:00-13:30, 15:30-16:00, 16:30-17:00
    tyler_busy = [(18, 22), (24, 25), (26, 27), (31, 32), (33, 34)]
    
    # Edward: 9:00-9:30, 10:00-11:00, 11:30-14:00, 14:30-15:30, 16:00-17:00
    edward_busy = [(18, 19), (20, 22), (23, 28), (29, 31), (32, 34)]
    
    # Janice prefers not after 13:00 (which is slot 26)
    janice_pref_max = 25  # 12:30 is the last preferred slot
    
    # Meeting duration: 30 minutes (1 slot)
    meeting_duration = 1
    
    # Define variable for meeting start time (in half-hour units)
    problem.addVariable("start_time", range(work_start, work_end - meeting_duration + 1))
    
    # Define constraints
    def is_available(start, busy_slots, duration):
        end = start + duration
        for busy_start, busy_end in busy_slots:
            if not (end <= busy_start or start >= busy_end):
                return False
        return True
    
    # Christine constraint
    problem.addConstraint(lambda start: is_available(start, christine_busy, meeting_duration), ["start_time"])
    
    # Bobby constraint  
    problem.addConstraint(lambda start: is_available(start, bobby_busy, meeting_duration), ["start_time"])
    
    # Elizabeth constraint
    problem.addConstraint(lambda start: is_available(start, elizabeth_busy, meeting_duration), ["start_time"])
    
    # Tyler constraint
    problem.addConstraint(lambda start: is_available(start, tyler_busy, meeting_duration), ["start_time"])
    
    # Edward constraint
    problem.addConstraint(lambda start: is_available(start, edward_busy, meeting_duration), ["start_time"])
    
    # Janice preference (not after 13:00)
    problem.addConstraint(lambda start: start <= janice_pref_max, ["start_time"])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        # Take the first solution
        start_slot = solutions[0]["start_time"]
        
        # Convert slot to time
        start_hour = start_slot // 2
        start_minute = (start_slot % 2) * 30
        
        end_slot = start_slot + meeting_duration
        end_hour = end_slot // 2
        end_minute = (end_slot % 2) * 30
        
        # Format output
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"Monday:{start_time_str}:{end_time_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()