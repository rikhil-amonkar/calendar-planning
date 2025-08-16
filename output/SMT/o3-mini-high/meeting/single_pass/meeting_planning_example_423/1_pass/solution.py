from z3 import Solver, Int, sat
import json

# Create a solver instance
s = Solver()

# We represent time in minutes after midnight.
# 9:00 AM is 540, etc.

# Define meeting start time variables for each friend:
# Elizabeth (Golden Gate Park)
E = Int('E')
# Brian (Financial District)
B = Int('B')
# Jason (Richmond District)
J = Int('J')
# Laura (Union Square)
L = Int('L')
# Melissa (North Beach)
M = Int('M')

# Meeting durations (in minutes)
dur_E = 105  # Elizabeth requires at least 105 minutes
dur_B = 15   # Brian requires at least 15 minutes
dur_J = 90   # Jason requires at least 90 minutes
dur_L = 75   # Laura requires at least 75 minutes
dur_M = 45   # Melissa requires at least 45 minutes

# Travel times (in minutes)
# Locations: Presidio (start), then:
# Golden Gate Park (Elizabeth), Financial District (Brian), Richmond District (Jason),
# Union Square (Laura), North Beach (Melissa)
t_P_to_G = 12   # Presidio -> Golden Gate Park
t_G_to_F = 26   # Golden Gate Park -> Financial District
t_F_to_R = 21   # Financial District -> Richmond District
t_R_to_U = 21   # Richmond District -> Union Square
t_U_to_N = 10   # Union Square -> North Beach

# Availability windows (in minutes after midnight)
# Elizabeth: Golden Gate Park from 08:45 to 21:30
avail_E_start = 8 * 60 + 45   # 525
avail_E_end   = 21 * 60 + 30  # 1290
# Brian: Financial District from 09:45 to 21:45
avail_B_start = 9 * 60 + 45   # 585
avail_B_end   = 21 * 60 + 45  # 1305
# Jason: Richmond District from 13:00 to 20:45
avail_J_start = 13 * 60       # 780
avail_J_end   = 20 * 60 + 45    # 1245
# Laura: Union Square from 14:15 to 19:30
avail_L_start = 14 * 60 + 15    # 855
avail_L_end   = 19 * 60 + 30    # 1170
# Melissa: North Beach from 18:45 to 20:15
avail_M_start = 18 * 60 + 45    # 1125
avail_M_end   = 20 * 60 + 15    # 1215

# Starting from the Presidio at 9:00 (540 minutes), and we need to travel to the meeting location.
# For Elizabeth, arriving at Golden Gate Park takes t_P_to_G = 12 minutes.
s.add(E >= 540 + t_P_to_G)  # E >= 552

# Each meeting must occur within the friend's availability window and be long enough.
s.add(E >= avail_E_start, E + dur_E <= avail_E_end)
s.add(B >= avail_B_start, B + dur_B <= avail_B_end)
s.add(J >= avail_J_start, J + dur_J <= avail_J_end)
s.add(L >= avail_L_start, L + dur_L <= avail_L_end)
s.add(M >= avail_M_start, M + dur_M <= avail_M_end)

# Add travel constraints between meetings in the chosen order:
# Order: Elizabeth (GGP) -> Brian (Financial District) -> Jason (Richmond District)
#        -> Laura (Union Square) -> Melissa (North Beach)

# After Elizabeth's meeting at Golden Gate Park, travel to Financial District takes 26 minutes.
s.add(B >= E + dur_E + t_G_to_F)

# From Brian at Financial District to Jason at Richmond District (travel time = 21)
s.add(J >= B + dur_B + t_F_to_R)

# From Jason at Richmond District to Laura at Union Square (travel time = 21)
s.add(L >= J + dur_J + t_R_to_U)

# From Laura at Union Square to Melissa at North Beach (travel time = 10)
s.add(M >= L + dur_L + t_U_to_N)

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    
    # Retrieve start times from the model
    start_E = m[E].as_long()
    start_B = m[B].as_long()
    start_J = m[J].as_long()
    start_L = m[L].as_long()
    start_M = m[M].as_long()
    
    # Calculate end times for each meeting
    end_E = start_E + dur_E
    end_B = start_B + dur_B
    end_J = start_J + dur_J
    end_L = start_L + dur_L
    end_M = start_M + dur_M

    # Function to convert minutes to HH:MM in 24-hour format
    def minutes_to_time(mins):
        hours = mins // 60
        minutes = mins % 60
        return f"{hours:02d}:{minutes:02d}"
    
    itinerary = [
        {"action": "meet", "person": "Elizabeth", "start_time": minutes_to_time(start_E), "end_time": minutes_to_time(end_E)},
        {"action": "meet", "person": "Brian",     "start_time": minutes_to_time(start_B), "end_time": minutes_to_time(end_B)},
        {"action": "meet", "person": "Jason",     "start_time": minutes_to_time(start_J), "end_time": minutes_to_time(end_J)},
        {"action": "meet", "person": "Laura",     "start_time": minutes_to_time(start_L), "end_time": minutes_to_time(end_L)},
        {"action": "meet", "person": "Melissa",   "start_time": minutes_to_time(start_M), "end_time": minutes_to_time(end_M)}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")