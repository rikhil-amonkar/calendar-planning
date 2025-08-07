from z3 import *

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Initialize Z3 integer variables for start times
h_start = Int('h_start')  # Helen start time in minutes from midnight
k_start = Int('k_start')  # Kimberly start time
p_start = Int('p_start')  # Patricia start time

# Initialize solver
s = Solver()

# Convert time constraints to minutes
nob_hill_arrival = 9 * 60  # 9:00 AM
helen_available_start = 7 * 60  # 7:00 AM (but we arrive at 9:08, so constraint starts from 9:08)
helen_available_end = 16 * 60 + 45  # 4:45 PM
kimberly_available_start = 16 * 60 + 30  # 4:30 PM
kimberly_available_end = 21 * 60  # 9:00 PM
patricia_available_start = 18 * 60  # 6:00 PM
patricia_available_end = 21 * 60 + 15  # 9:15 PM

# Travel times in minutes
travel_nob_hill_to_north_beach = 8
travel_north_beach_to_fisherman_wharf = 5
travel_fisherman_wharf_to_bayview = 26

# Meeting durations in minutes
helen_duration = 120
kimberly_duration = 45
patricia_duration = 120

# Constraints for Helen
s.add(h_start >= nob_hill_arrival + travel_nob_hill_to_north_beach)  # Arrive at North Beach at 9:08 AM
s.add(h_start >= helen_available_start)  # Available from 7:00 AM, but we arrive at 9:08
s.add(h_start + helen_duration <= helen_available_end)  # Must end by 4:45 PM

# Constraints for Kimberly
s.add(k_start >= h_start + helen_duration + travel_north_beach_to_fisherman_wharf)  # Travel after Helen's meeting
s.add(k_start >= kimberly_available_start)  # Available from 4:30 PM
s.add(k_start + kimberly_duration <= kimberly_available_end)  # Must end by 9:00 PM

# Constraints for Patricia
s.add(p_start >= k_start + kimberly_duration + travel_fisherman_wharf_to_bayview)  # Travel after Kimberly's meeting
s.add(p_start >= patricia_available_start)  # Available from 6:00 PM
s.add(p_start + patricia_duration <= patricia_available_end)  # Must end by 9:15 PM

# Additional constraint to ensure Kimberly ends in time for Patricia's meeting
s.add(k_start + kimberly_duration + travel_fisherman_wharf_to_bayview <= patricia_available_end - patricia_duration)

# Check if a solution exists
if s.check() == sat:
    model = s.model()
    h_start_val = model[h_start].as_long()
    k_start_val = model[k_start].as_long()
    p_start_val = model[p_start].as_long()
    
    # Create itinerary
    itinerary = [
        {
            "action": "meet",
            "person": "Helen",
            "start_time": minutes_to_time(h_start_val),
            "end_time": minutes_to_time(h_start_val + helen_duration)
        },
        {
            "action": "meet",
            "person": "Kimberly",
            "start_time": minutes_to_time(k_start_val),
            "end_time": minutes_to_time(k_start_val + kimberly_duration)
        },
        {
            "action": "meet",
            "person": "Patricia",
            "start_time": minutes_to_time(p_start_val),
            "end_time": minutes_to_time(p_start_val + patricia_duration)
        }
    ]
    
    # Output the solution in JSON format
    print({
        "itinerary": itinerary
    })
else:
    print("No feasible schedule found.")