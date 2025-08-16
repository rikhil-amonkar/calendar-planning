from z3 import *
import json

def minutes_to_time(m):
    # m is the number of minutes after 9:00.
    # 9:00 AM is 9*60 = 540 minutes after midnight.
    total = m + 540
    hour = total // 60
    minute = total % 60
    return f"{hour:02d}:{minute:02d}"

# Create a Z3 solver instance
solver = Solver()

# Define decision variables representing the meeting start times (in minutes after 9:00 AM)
s_sandra   = Int('s_sandra')
s_carol    = Int('s_carol')
s_brian    = Int('s_brian')
s_kimberly = Int('s_kimberly')
s_kenneth  = Int('s_kenneth')
s_laura    = Int('s_laura')
s_linda    = Int('s_linda')
s_karen    = Int('s_karen')
s_paul     = Int('s_paul')

# Minimum meeting durations (in minutes)
durations = {
    "Sandra":   60,
    "Carol":    60,
    "Brian":    75,
    "Kimberly": 30,
    "Kenneth":  30,
    "Laura":    30,
    "Linda":    30,
    "Karen":    75,
    "Paul":     15
}

# Friend availability windows, given as (earliest start, latest end) in minutes after 9:00 AM.
# For a meeting of duration d, we need: start >= available_start  and start + d <= available_end.
availability = {
    "Sandra":   (15, 570),   # 9:15 AM to 6:30 PM
    "Carol":    (75, 180),   # 10:15 AM to 12:00 PM
    "Brian":    (60, 750),   # 10:00 AM to 9:30 PM
    "Kimberly": (315, 780),  # 14:15 PM to 22:00 PM
    "Kenneth":  (345, 435),  # 14:45 PM to 16:15 PM
    "Laura":    (435, 690),  # 16:15 PM to 20:30 PM
    "Linda":    (540, 780),  # 18:00 PM to 22:00 PM
    "Karen":    (570, 780),  # 18:30 PM to 22:00 PM
    "Paul":     (720, 750)   # 21:00 PM to 21:30 PM
}

# Add availability constraints for each meeting:
solver.add(s_sandra   >= availability["Sandra"][0],   s_sandra   + durations["Sandra"]   <= availability["Sandra"][1])
solver.add(s_carol    >= availability["Carol"][0],    s_carol    + durations["Carol"]    <= availability["Carol"][1])
solver.add(s_brian    >= availability["Brian"][0],    s_brian    + durations["Brian"]    <= availability["Brian"][1])
solver.add(s_kimberly >= availability["Kimberly"][0], s_kimberly + durations["Kimberly"] <= availability["Kimberly"][1])
solver.add(s_kenneth  >= availability["Kenneth"][0],  s_kenneth  + durations["Kenneth"]  <= availability["Kenneth"][1])
solver.add(s_laura    >= availability["Laura"][0],    s_laura    + durations["Laura"]    <= availability["Laura"][1])
solver.add(s_linda    >= availability["Linda"][0],    s_linda    + durations["Linda"]    <= availability["Linda"][1])
solver.add(s_karen    >= availability["Karen"][0],    s_karen    + durations["Karen"]    <= availability["Karen"][1])
solver.add(s_paul     >= availability["Paul"][0],     s_paul     + durations["Paul"]     <= availability["Paul"][1])

# Our chosen meeting order (with friend and meeting location):
# 1. Sandra    (Meet at Nob Hill)
# 2. Carol     (Meet at Financial District)
# 3. Brian     (Meet at Presidio)
# 4. Kimberly  (Meet at Richmond District)
# 5. Kenneth   (Meet at The Castro)
# 6. Laura     (Meet at Mission District)
# 7. Linda     (Meet at Marina District)
# 8. Karen     (Meet at Russian Hill)
# 9. Paul      (Meet at Alamo Square)
#
# Travel times (in minutes) between locations:
travel = {
    "PH_to_Sandra":       8,   # Pacific Heights -> Nob Hill (Sandra)
    "Sandra_to_Carol":    9,   # Nob Hill -> Financial District
    "Carol_to_Brian":     22,  # Financial District -> Presidio
    "Brian_to_Kimberly":  7,   # Presidio -> Richmond District
    "Kimberly_to_Kenneth":16,   # Richmond District -> The Castro
    "Kenneth_to_Laura":   7,   # The Castro -> Mission District
    "Laura_to_Linda":     19,  # Mission District -> Marina District
    "Linda_to_Karen":     8,   # Marina District -> Russian Hill
    "Karen_to_Paul":      15   # Russian Hill -> Alamo Square
}

# Add travel constraints:
# You start at Pacific Heights at 9:00 (minute 0). The first meeting can't begin before you travel to the location.
solver.add(s_sandra >= travel["PH_to_Sandra"])

# For consecutive meetings, the next meeting's start time must be no earlier than the finish time of the previous meeting plus travel time.
solver.add(s_carol    >= s_sandra   + durations["Sandra"]   + travel["Sandra_to_Carol"])
solver.add(s_brian    >= s_carol    + durations["Carol"]    + travel["Carol_to_Brian"])
solver.add(s_kimberly >= s_brian    + durations["Brian"]    + travel["Brian_to_Kimberly"])
solver.add(s_kenneth  >= s_kimberly + durations["Kimberly"] + travel["Kimberly_to_Kenneth"])
solver.add(s_laura    >= s_kenneth  + durations["Kenneth"]  + travel["Kenneth_to_Laura"])
solver.add(s_linda    >= s_laura    + durations["Laura"]    + travel["Laura_to_Linda"])
solver.add(s_karen    >= s_linda    + durations["Linda"]    + travel["Linda_to_Karen"])
solver.add(s_paul     >= s_karen    + durations["Karen"]    + travel["Karen_to_Paul"])

# Check for satisfiability and extract the model if one is found
if solver.check() == sat:
    model = solver.model()
    # Prepare the meeting itinerary.
    # Each meeting will have a start time and an end time computed as start + duration.
    meetings = [
        ("Sandra",   model[s_sandra].as_long(),   durations["Sandra"]),
        ("Carol",    model[s_carol].as_long(),    durations["Carol"]),
        ("Brian",    model[s_brian].as_long(),    durations["Brian"]),
        ("Kimberly", model[s_kimberly].as_long(), durations["Kimberly"]),
        ("Kenneth",  model[s_kenneth].as_long(),  durations["Kenneth"]),
        ("Laura",    model[s_laura].as_long(),    durations["Laura"]),
        ("Linda",    model[s_linda].as_long(),    durations["Linda"]),
        ("Karen",    model[s_karen].as_long(),    durations["Karen"]),
        ("Paul",     model[s_paul].as_long(),     durations["Paul"])
    ]
    
    # (The order is already imposed via the travel constraints.)
    itinerary = []
    for person, start, dur in meetings:
        start_time = minutes_to_time(start)
        end_time   = minutes_to_time(start + dur)
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": start_time,
            "end_time": end_time
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")