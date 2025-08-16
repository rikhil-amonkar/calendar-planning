from z3 import *
import json

# Helper function: convert minutes since midnight to "HH:MM" format.
def minutes_to_HHMM(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define meeting parameters (in minutes)
# Arrival at Union Square: 9:00AM -> 9*60 = 540
start_union_square = 540

# Friend information:
# Format: (location, available_start, available_end, min_meeting_duration)
# Times in minutes after midnight.
# Sandra: Chinatown, available 7:15AM (435) to 7:15PM (1155), duration >= 75
# Nancy: Marina District, available 11:00AM (660) to 8:15PM (1215), duration >= 105
# Joseph: Haight-Ashbury, available 12:30PM (750) to 7:45PM (1185), duration >= 90
# Karen: Nob Hill, available 9:15PM (1275) to 9:45PM (1305), duration >= 30

sandra_avail_start, sandra_avail_end, sandra_min = 435, 1155, 75
nancy_avail_start, nancy_avail_end, nancy_min = 660, 1215, 105
joseph_avail_start, joseph_avail_end, joseph_min = 750, 1185, 90
karen_avail_start, karen_avail_end, karen_min = 1275, 1305, 30

# Travel times (in minutes) between locations.
# We have a symmetric travel plan for our chosen order.
# Our chosen order (based on availabilities and travel distances):
#   1. Sandra (Chinatown)
#   2. Nancy (Marina District)
#   3. Joseph (Haight-Ashbury)
#   4. Karen (Nob Hill)
#
# Travel times we need:
# - Union Square -> Chinatown: 7 minutes.
# - Chinatown -> Marina District: 12 minutes.  (from the table: Chinatown to Marina District = 12)
# - Marina District -> Haight-Ashbury: 16 minutes. (from the table: Marina District to Haight-Ashbury = 16)
# - Haight-Ashbury -> Nob Hill: 15 minutes. (from the table: Haight-Ashbury to Nob Hill = 15)

travel_US_to_Chinatown = 7
travel_Chinatown_to_Marina = 12
travel_Marina_to_Haight = 16
travel_Haight_to_NobHill = 15

# Create Z3 integer variables for the start time (in minutes) for each meeting.
sandra_start = Int('sandra_start')
nancy_start = Int('nancy_start')
joseph_start = Int('joseph_start')
karen_start = Int('karen_start')

# Create an Optimize object.
opt = Optimize()

# --- Constraints for Sandra (Chinatown) ---
# Must allow time to travel from Union Square to Chinatown.
opt.add(sandra_start >= start_union_square + travel_US_to_Chinatown)
# Also, Sandra is only available from her availability start.
opt.add(sandra_start >= sandra_avail_start)
# Meeting must finish before Sandra’s availability ends.
opt.add(sandra_start + sandra_min <= sandra_avail_end)

# --- Constraints for Nancy (Marina District) ---
# Must arrive after finishing Sandra's meeting plus travel from Chinatown to Marina District.
opt.add(nancy_start >= sandra_start + sandra_min + travel_Chinatown_to_Marina)
# Nancy is available from 11:00AM.
opt.add(nancy_start >= nancy_avail_start)
# Meeting must finish before Nancy’s availability ends.
opt.add(nancy_start + nancy_min <= nancy_avail_end)

# --- Constraints for Joseph (Haight-Ashbury) ---
# Must arrive after Nancy's meeting plus travel from Marina District to Haight-Ashbury.
opt.add(joseph_start >= nancy_start + nancy_min + travel_Marina_to_Haight)
# Joseph is available from 12:30PM.
opt.add(joseph_start >= joseph_avail_start)
# Meeting must finish before Joseph’s availability ends.
opt.add(joseph_start + joseph_min <= joseph_avail_end)

# --- Constraints for Karen (Nob Hill) ---
# Must arrive after Joseph's meeting plus travel from Haight-Ashbury to Nob Hill.
opt.add(karen_start >= joseph_start + joseph_min + travel_Haight_to_NobHill)
# Karen is only available starting 9:15PM.
opt.add(karen_start >= karen_avail_start)
# Meeting must finish before Karen’s availability ends.
opt.add(karen_start + karen_min <= karen_avail_end)

# For an "optimal" (minimal overall schedule) solution we minimize Karen's meeting start.
opt.minimize(karen_start)

# Check if the constraints are satisfiable and obtain model.
if opt.check() == sat:
    model = opt.model()
    sandra_s = model[sandra_start].as_long()
    nancy_s = model[nancy_start].as_long()
    joseph_s = model[joseph_start].as_long()
    karen_s = model[karen_start].as_long()
    
    itinerary = [
        {
            "action": "meet",
            "person": "Sandra",
            "start_time": minutes_to_HHMM(sandra_s),
            "end_time": minutes_to_HHMM(sandra_s + sandra_min)
        },
        {
            "action": "meet",
            "person": "Nancy",
            "start_time": minutes_to_HHMM(nancy_s),
            "end_time": minutes_to_HHMM(nancy_s + nancy_min)
        },
        {
            "action": "meet",
            "person": "Joseph",
            "start_time": minutes_to_HHMM(joseph_s),
            "end_time": minutes_to_HHMM(joseph_s + joseph_min)
        },
        {
            "action": "meet",
            "person": "Karen",
            "start_time": minutes_to_HHMM(karen_s),
            "end_time": minutes_to_HHMM(karen_s + karen_min)
        }
    ]
    
    # Output the final itinerary as a JSON-formatted dictionary.
    print(json.dumps({"itinerary": itinerary}, indent=4))
else:
    print("No solution found")