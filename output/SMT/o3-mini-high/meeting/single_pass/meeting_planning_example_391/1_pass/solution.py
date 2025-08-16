import json
from z3 import *

def minutes_to_time(m):
    # convert minutes after midnight to "HH:MM" string
    hours = m // 60
    minutes = m % 60
    return "{:02d}:{:02d}".format(hours, minutes)

# Create an Optimize solver (allows objectives) 
solver = Optimize()

# ------ Define decision variables (times are in minutes after midnight) --------
# For each friend meeting we have a start and end time.
K_s = Int('K_s')   # Kevin start (at Alamo Square)
K_e = Int('K_e')   # Kevin end
Ki_s = Int('Ki_s') # Kimberly start (at Russian Hill)
Ki_e = Int('Ki_e') # Kimberly end
J_s = Int('J_s')   # Joseph start (at Presidio)
J_e = Int('J_e')   # Joseph end
T_s = Int('T_s')   # Thomas start (at Financial District)
T_e = Int('T_e')   # Thomas end

# A Boolean decision for the order in which you meet the two morning friends.
# True means: Meet Kevin first then Kimberly.
# False means: Meet Kimberly first then Kevin.
order_k_first = Bool('order_k_first')

# ------ Constants and Friend Availabilities -----------
# You start your day in the Sunset District at 9:00AM = 540 minutes.
start_time = 540

# Friend availability windows (times in minutes after midnight):
# Kevin is at Alamo Square from 8:15 to 21:30 => [495, 1290]
solver.add(K_s >= 495, K_e <= 1290)
# Kimberly is at Russian Hill from 8:45 to 12:30 => [525, 750]
solver.add(Ki_s >= 525, Ki_e <= 750)
# Joseph is at Presidio from 18:30 to 19:15 => [1110, 1155]
solver.add(J_s >= 1110, J_e <= 1155)
# Thomas is at Financial District from 19:00 to 21:45 => [1140, 1305]
solver.add(T_s >= 1140, T_e <= 1305)

# ------ Minimum Meeting Durations ----------
solver.add(K_e - K_s >= 75)   # Kevin: 75 minutes
solver.add(Ki_e - Ki_s >= 30)   # Kimberly: 30 minutes
solver.add(J_e - J_s >= 45)     # Joseph: 45 minutes
solver.add(T_e - T_s >= 45)     # Thomas: 45 minutes

# ------ Travel Times Between Locations (all in minutes) -----------
# From your starting location in Sunset District to:
#   Alamo Square: 17 minutes.
#   Russian Hill: 24 minutes.
sunset_to_alamo  = 17
sunset_to_russian = 24

# In the morning the order is flexible.
# If you meet Kevin first (order_k_first True):
#   • You travel from Sunset->Alamo (17 mins): K_s ≥ 540+17.
#   • Then from Alamo Square to Russian Hill takes 13 mins: Ki_s ≥ K_e + 13.
# If you meet Kimberly first (order_k_first False):
#   • You travel from Sunset->Russian Hill (24 mins): Ki_s ≥ 540+24.
#   • Then from Russian Hill to Alamo Square takes 15 mins: K_s ≥ Ki_e + 15.
solver.add(If(order_k_first, K_s >= start_time + sunset_to_alamo, Ki_s >= start_time + sunset_to_russian))
solver.add(If(order_k_first, Ki_s >= K_e + 13, K_s >= Ki_e + 15))

# Let morning_end denote the finish time of the last morning meeting.
# (i.e. if order_k_first True then this is Kimberly’s ending time; otherwise Kevin’s ending time)
morning_end = If(order_k_first, Ki_e, K_e)

# To get to Joseph’s meeting (at Presidio) in the evening:
# From the last morning location to Presidio:
#   • If you ended with Kimberly (Russian Hill) travel takes 14 minutes.
#   • If you ended with Kevin (Alamo Square) travel takes 18 minutes.
solver.add(J_s >= If(order_k_first, morning_end + 14, morning_end + 18))

# Evening travel – After Joseph at Presidio, travel to Thomas at Financial District takes 23 minutes.
solver.add(T_s >= J_e + 23)

# ------ “Tighten” meeting durations to their minimum (optimal waiting) --------
# In an optimal schedule you’d want to meet exactly the minimum time.
solver.add(K_e == K_s + 75)
solver.add(Ki_e == Ki_s + 30)
solver.add(J_e == J_s + 45)
solver.add(T_e == T_s + 45)

# ------ Objectives ----------
# Since your goal is to meet as many friends as possible with minimal idle waiting,
# we expect to schedule all 4. In addition, we can “pull” the morning meetings as early as possible.
# We do so by minimizing the end of your morning meetings.
solver.minimize(morning_end)
# Also, for a tie–breaker, minimize the sum of meeting start times.
solver.minimize(K_s + Ki_s + J_s + T_s)

# ------ Solve the Model --------
if solver.check() == sat:
    model = solver.model()
    # Extract times from the model
    K_s_val = model[K_s].as_long()
    K_e_val = model[K_e].as_long()
    Ki_s_val = model[Ki_s].as_long()
    Ki_e_val = model[Ki_e].as_long()
    J_s_val = model[J_s].as_long()
    J_e_val = model[J_e].as_long()
    T_s_val = model[T_s].as_long()
    T_e_val = model[T_e].as_long()
    order = model.evaluate(order_k_first)
    
    itinerary = []
    # Morning meetings order:
    # If order is True: meet Kevin (at Alamo Square) then Kimberly (at Russian Hill)
    if is_true(order):
        itinerary.append({
            "action": "meet",
            "person": "Kevin",
            "start_time": minutes_to_time(K_s_val),
            "end_time": minutes_to_time(K_e_val)
        })
        itinerary.append({
            "action": "meet",
            "person": "Kimberly",
            "start_time": minutes_to_time(Ki_s_val),
            "end_time": minutes_to_time(Ki_e_val)
        })
    else:
        itinerary.append({
            "action": "meet",
            "person": "Kimberly",
            "start_time": minutes_to_time(Ki_s_val),
            "end_time": minutes_to_time(Ki_e_val)
        })
        itinerary.append({
            "action": "meet",
            "person": "Kevin",
            "start_time": minutes_to_time(K_s_val),
            "end_time": minutes_to_time(K_e_val)
        })
    
    # Evening meetings order (fixed): Joseph then Thomas.
    itinerary.append({
        "action": "meet",
        "person": "Joseph",
        "start_time": minutes_to_time(J_s_val),
        "end_time": minutes_to_time(J_e_val)
    })
    itinerary.append({
        "action": "meet",
        "person": "Thomas",
        "start_time": minutes_to_time(T_s_val),
        "end_time": minutes_to_time(T_e_val)
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")