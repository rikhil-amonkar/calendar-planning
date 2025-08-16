from z3 import *
import json

def minutes_to_HHMM(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02}:{minutes:02}"

# Create a Z3 solver instance
s = Solver()

# Define meeting time variables (minutes after midnight)
t_T_start = Int('t_T_start')  # Timothy meeting start (Embarcadero)
t_T_end   = Int('t_T_end')    # Timothy meeting end

t_P_start = Int('t_P_start')  # Patricia meeting start (Nob Hill)
t_P_end   = Int('t_P_end')    # Patricia meeting end

t_A_start = Int('t_A_start')  # Ashley meeting start (Mission District)
t_A_end   = Int('t_A_end')    # Ashley meeting end

# Starting location: Russian Hill arrival time at 09:00
RH_arrival = 9 * 60  # 540 minutes

# Availability windows (in minutes after midnight)
Timothy_avail_start = 9 * 60 + 45    # 09:45 -> 585
Timothy_avail_end   = 17 * 60 + 45     # 17:45 -> 1065

Patricia_avail_start = 18 * 60 + 30    # 18:30 -> 1110
Patricia_avail_end   = 21 * 60 + 45      # 21:45 -> 1305

Ashley_avail_start = 20 * 60 + 30      # 20:30 -> 1230
Ashley_avail_end   = 21 * 60 + 15      # 21:15 -> 1275

# Travel times between locations (in minutes)
# From Russian Hill to Embarcadero: 8 minutes
# From Embarcadero to Nob Hill: 10 minutes
# From Nob Hill to Mission District: 13 minutes

# ----------------------------
# Timothy meeting constraints (at Embarcadero)
# We leave Russian Hill at 09:00 and travel to Embarcadero.
s.add(t_T_start >= Timothy_avail_start)      # Cannot start before Timothy is available (09:45)
s.add(t_T_start >= RH_arrival + 8)             # Must account for travel time (09:00 + 8 = 09:08)
s.add(t_T_end   >= t_T_start + 120)            # Minimum meeting duration 120 minutes
s.add(t_T_end   <= Timothy_avail_end)          # Must finish before Timothy leaves (17:45)

# ----------------------------
# Patricia meeting constraints (at Nob Hill)
# After finishing with Timothy, travel from Embarcadero to Nob Hill takes 10 minutes.
s.add(t_P_start >= Patricia_avail_start)       # Cannot start before Patricia is available (18:30)
s.add(t_P_start >= t_T_end + 10)                # Must allow travel time from Embarcadero (10 minutes)
s.add(t_P_end   >= t_P_start + 90)              # Minimum meeting duration 90 minutes
s.add(t_P_end   <= Patricia_avail_end)          # Must finish before Patricia leaves (21:45)

# ----------------------------
# Ashley meeting constraints (at Mission District)
# After Patricia, travel from Nob Hill to Mission District takes 13 minutes.
s.add(t_A_start >= Ashley_avail_start)         # Cannot start before Ashley is available (20:30)
s.add(t_A_start >= t_P_end + 13)                # Must allow travel time from Nob Hill (13 minutes)
s.add(t_A_end   >= t_A_start + 45)              # Minimum meeting duration 45 minutes
s.add(t_A_end   <= Ashley_avail_end)            # Must finish before Ashley leaves (21:15)

# Check if there is a solution and print the itinerary if found
if s.check() == sat:
    m = s.model()
    itinerary = [
        {
            "action": "meet",
            "person": "Timothy",
            "start_time": minutes_to_HHMM(m[t_T_start].as_long()),
            "end_time": minutes_to_HHMM(m[t_T_end].as_long())
        },
        {
            "action": "meet",
            "person": "Patricia",
            "start_time": minutes_to_HHMM(m[t_P_start].as_long()),
            "end_time": minutes_to_HHMM(m[t_P_end].as_long())
        },
        {
            "action": "meet",
            "person": "Ashley",
            "start_time": minutes_to_HHMM(m[t_A_start].as_long()),
            "end_time": minutes_to_HHMM(m[t_A_end].as_long())
        }
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found")