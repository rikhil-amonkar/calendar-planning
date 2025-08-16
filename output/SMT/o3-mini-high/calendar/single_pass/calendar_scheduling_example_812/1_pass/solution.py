from z3 import Int, Optimize, Or

def main():
    # Create an optimizer instance
    opt = Optimize()
    
    # Define variables:
    # meeting_day is an integer: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday.
    meeting_day = Int("meeting_day")
    # meeting_start is the start time in minutes after 9:00.
    # Workday is 9:00 to 17:00 which is 480 minutes. With a meeting duration of 30 minutes,
    # meeting_start can be at most 450.
    meeting_start = Int("meeting_start")
    
    # Domain constraints
    opt.add(meeting_day >= 0, meeting_day <= 3)
    opt.add(meeting_start >= 0, meeting_start <= 450)
    opt.add(meeting_start + 30 <= 480)
    
    # Helper function: a meeting does not conflict with an appointment.
    # If the meeting is on the same day as the appointment, then the meeting must end
    # before the appointment starts OR start after the appointment ends.
    def no_overlap(day, app_start, app_end):
        return Or(meeting_day != day, meeting_start + 30 <= app_start, meeting_start >= app_end)
    
    # Add Mary’s appointments:
    # Mary has no meeting on Monday.
    # Tuesday (day=1): [10:00, 10:30] and [15:30, 16:00]
    # (Times are relative to 9:00: 10:00 -> 60, 10:30 -> 90; 15:30 -> 390, 16:00 -> 400)
    opt.add(no_overlap(1, 60, 90))
    opt.add(no_overlap(1, 390, 400))
    
    # Wednesday (day=2): [9:30, 10:00] and [15:00, 15:30]
    # 9:30 -> 30, 10:00 -> 60; 15:00 -> 360, 15:30 -> 390
    opt.add(no_overlap(2, 30, 60))
    opt.add(no_overlap(2, 360, 390))
    
    # Thursday (day=3): [9:00, 10:00] and [10:30, 11:30]
    # 9:00 -> 0, 10:00 -> 60; 10:30 -> 90, 11:30 -> 150
    opt.add(no_overlap(3, 0, 60))
    opt.add(no_overlap(3, 90, 150))
    
    # Add Alexis’s appointments:
    # Monday (day=0): [9:00, 10:00], [10:30, 12:00], and [12:30, 16:30]
    # 9:00 -> 0, 10:00 -> 60; 10:30 -> 90, 12:00 -> 180; 12:30 -> 210, 16:30 -> 450
    opt.add(no_overlap(0, 0, 60))
    opt.add(no_overlap(0, 90, 180))
    opt.add(no_overlap(0, 210, 450))
    
    # Tuesday (day=1): [9:00, 10:00], [10:30, 11:30], [12:00, 15:30], [16:00, 17:00]
    # 9:00 -> 0, 10:00 -> 60; 10:30 -> 90, 11:30 -> 150; 12:00 -> 180, 15:30 -> 390; 16:00 -> 420, 17:00 -> 480
    opt.add(no_overlap(1, 0, 60))
    opt.add(no_overlap(1, 90, 150))
    opt.add(no_overlap(1, 180, 390))
    opt.add(no_overlap(1, 420, 480))
    
    # Wednesday (day=2): [9:00, 11:00] and [11:30, 17:00]
    # 9:00 -> 0, 11:00 -> 120; 11:30 -> 150, 17:00 -> 480
    opt.add(no_overlap(2, 0, 120))
    opt.add(no_overlap(2, 150, 480))
    
    # Thursday (day=3): [10:00, 12:00], [14:00, 14:30], [15:30, 16:00], and [16:30, 17:00]
    # 10:00 -> 60, 12:00 -> 180; 14:00 -> 300, 14:30 -> 330; 15:30 -> 390, 16:00 -> 420; 16:30 -> 450, 17:00 -> 480
    opt.add(no_overlap(3, 60, 180))
    opt.add(no_overlap(3, 300, 330))
    opt.add(no_overlap(3, 390, 420))
    opt.add(no_overlap(3, 450, 480))
    
    # To meet at the earliest availability, we minimize the combined value of day and start time.
    # Multiply day by 1000 to ensure that earlier days (Monday=0) are prioritized over later days,
    # and then use meeting_start for the tie-breaker.
    cost = meeting_day * 1000 + meeting_start
    opt.minimize(cost)
    
    # Solve for a valid meeting time.
    if opt.check() == 'sat':
        model = opt.model()
        day_val = model[meeting_day].as_long()
        start_val = model[meeting_start].as_long()
        
        # Map integer day value to day names.
        day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
        day_str = day_names[day_val]
        
        # Convert meeting_start (minutes after 9:00) to an actual time.
        total_start_minutes = 9 * 60 + start_val
        start_hour = total_start_minutes // 60
        start_minute = total_start_minutes % 60
        
        # The meeting lasts 30 minutes.
        total_end_minutes = total_start_minutes + 30
        end_hour = total_end_minutes // 60
        end_minute = total_end_minutes % 60
        
        # Format the times to "HH:MM".
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        # Print the solution.
        print("SOLUTION:")
        print("Day:", day_str)
        print("Start Time:", start_time_str)
        print("End Time:", end_time_str)
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()