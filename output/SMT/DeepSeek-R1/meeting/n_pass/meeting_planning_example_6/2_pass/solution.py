from z3 import *

def main():
    # Define the variables
    t0 = Int('t0')   # departure time from Fisherman's Wharf (minutes after 9:00 AM)
    depart_NH = Int('depart_NH') # departure time from Nob Hill (minutes after 9:00 AM)
    
    s = Solver()
    
    # Constraints
    s.add(t0 >= 0)  # must leave Fisherman's Wharf after 9:00 AM
    arrive_NH = t0 + 11  # arrival time at Nob Hill
    s.add(depart_NH >= arrive_NH)  # must leave Nob Hill after arriving
    
    # Kenneth's availability window: 315 to 645 minutes (2:15 PM to 7:45 PM)
    s.add(arrive_NH <= 645)  # must arrive at Nob Hill by 7:45 PM
    s.add(depart_NH >= 315)  # must leave Nob Hill after 2:15 PM
    
    # Overlap constraint: at least 90 minutes
    start_meeting = If(arrive_NH < 315, 315, arrive_NH)
    end_meeting = If(depart_NH > 645, 645, depart_NH)
    overlap = end_meeting - start_meeting
    s.add(overlap >= 90)
    
    if s.check() == sat:
        m = s.model()
        t0_val = m[t0].as_long()
        depart_NH_val = m[depart_NH].as_long()
        arrive_NH_val = t0_val + 11
        
        # Function to convert minutes since 9:00 AM to formatted time string (12-hour with AM/PM)
        def format_time(minutes_since_9am):
            total_minutes = minutes_since_9am
            total_hours = 9 + total_minutes // 60
            minutes = total_minutes % 60
            hour12 = total_hours % 12
            if hour12 == 0:
                hour12 = 12
            period = "AM" if total_hours < 12 else "PM"
            # Adjust period for afternoon/evening
            if total_hours >= 12:
                period = "PM"
                if total_hours > 12:
                    hour12 = total_hours % 12
            else:
                period = "AM"
            return f"{hour12}:{minutes:02d} {period}"
        
        leave_fw_time = format_time(t0_val)
        arrive_nh_time = format_time(arrive_NH_val)
        leave_nh_time = format_time(depart_NH_val)
        
        # Calculate actual meeting start and end times
        start_meeting_val = max(arrive_NH_val, 315)
        end_meeting_val = min(depart_NH_val, 645)
        meeting_duration = end_meeting_val - start_meeting_val
        
        print("SOLUTION:")
        print(f"Leave Fisherman's Wharf at {leave_fw_time}")
        print(f"Arrive at Nob Hill at {arrive_nh_time}")
        print(f"Leave Nob Hill at {leave_nh_time}")
        print(f"Meeting time with Kenneth: {meeting_duration} minutes (from {format_time(start_meeting_val)} to {format_time(end_meeting_val)})")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()