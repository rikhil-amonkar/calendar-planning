from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Time in minutes from 9:00 AM
    s_start = Int('s_start')  # Start time for meeting Stephanie
    j_start = Int('j_start')  # Start time for meeting John

    # Stephanie's meeting must be 90 minutes and within her availability (9:05 AM to 10:00 AM start to end by 11:30 AM)
    s.add(s_start >= 5)  # 9:05 AM is 5 minutes from 9:00 AM
    s.add(s_start + 90 <= 150)  # 11:30 AM is 150 minutes from 9:00 AM

    # John's meeting must be 30 minutes and start after 10:15 AM (75 minutes from 9:00 AM)
    s.add(j_start >= s_start + 90 + 17)  # Travel from Financial District to Alamo Square takes 17 minutes
    s.add(j_start >= 75)  # John available from 10:15 AM (75 minutes)
    s.add(j_start + 30 <= 705)  # John available until 8:45 PM (705 minutes), though not binding

    # Check for a feasible solution
    if s.check() == sat:
        m = s.model()
        s_start_val = m[s_start].as_long()
        j_start_val = m[j_start].as_long()
        
        # Calculate end times
        s_end_val = s_start_val + 90
        j_end_val = j_start_val + 30
        
        # Convert times to 24-hour format
        def format_time(minutes):
            total_minutes = 9 * 60 + minutes
            hours = total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours:02d}:{minutes:02d}"
        
        s_start_str = format_time(s_start_val)
        s_end_str = format_time(s_end_val)
        j_start_str = format_time(j_start_val)
        j_end_str = format_time(j_end_val)
        
        # Prepare itinerary
        itinerary = [
            {"action": "meet", "person": "Stephanie", "start_time": s_start_str, "end_time": s_end_str},
            {"action": "meet", "person": "John", "start_time": j_start_str, "end_time": j_end_str}
        ]
        
        # Output as JSON-formatted dictionary
        import json
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No feasible schedule found.")

if __name__ == "__main__":
    main()