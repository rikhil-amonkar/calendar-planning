from z3 import *
import json

def main():
    # Meeting data: each friend with location, availability window (in minutes from midnight), and minimum meeting duration.
    # Times are in minutes from midnight.
    # 9:00 AM = 540.
    friends = [
        {"name": "Matthew", "location": "Bayview", "avail_start": 1155, "avail_end": 1320, "duration": 120},
        {"name": "Karen", "location": "Chinatown", "avail_start": 1155, "avail_end": 1275, "duration": 90},
        {"name": "Sarah", "location": "Alamo Square", "avail_start": 1200, "avail_end": 1305, "duration": 105},
        {"name": "Jessica", "location": "Nob Hill", "avail_start": 990, "avail_end": 1125, "duration": 120},
        {"name": "Stephanie", "location": "Presidio", "avail_start": 450, "avail_end": 615, "duration": 60},
        {"name": "Mary", "location": "Union Square", "avail_start": 1005, "avail_end": 1290, "duration": 60},
        {"name": "Charles", "location": "The Castro", "avail_start": 990, "avail_end": 1320, "duration": 105},
        {"name": "Nancy", "location": "North Beach", "avail_start": 885, "avail_end": 1200, "duration": 15},
        {"name": "Thomas", "location": "Fisherman's Wharf", "avail_start": 810, "avail_end": 1140, "duration": 30},
        {"name": "Brian", "location": "Marina District", "avail_start": 735, "avail_end": 1080, "duration": 60}
    ]
    
    # Travel times in minutes between locations.
    # Note: The travel time from one location to another can differ from the reverse direction.
    travel = {
       "Embarcadero": {
           "Bayview": 21,
           "Chinatown": 7,
           "Alamo Square": 19,
           "Nob Hill": 10,
           "Presidio": 20,
           "Union Square": 10,
           "The Castro": 25,
           "North Beach": 5,
           "Fisherman's Wharf": 6,
           "Marina District": 12
       },
       "Bayview": {
           "Embarcadero": 19,
           "Chinatown": 19,
           "Alamo Square": 16,
           "Nob Hill": 20,
           "Presidio": 32,
           "Union Square": 18,
           "The Castro": 19,
           "North Beach": 22,
           "Fisherman's Wharf": 25,
           "Marina District": 27
       },
       "Chinatown": {
           "Embarcadero": 5,
           "Bayview": 20,
           "Alamo Square": 17,
           "Nob Hill": 9,
           "Presidio": 19,
           "Union Square": 7,
           "The Castro": 22,
           "North Beach": 3,
           "Fisherman's Wharf": 8,
           "Marina District": 12
       },
       "Alamo Square": {
           "Embarcadero": 16,
           "Bayview": 16,
           "Chinatown": 15,
           "Nob Hill": 11,
           "Presidio": 17,
           "Union Square": 14,
           "The Castro": 8,
           "North Beach": 15,
           "Fisherman's Wharf": 19,
           "Marina District": 15
       },
       "Nob Hill": {
           "Embarcadero": 9,
           "Bayview": 19,
           "Chinatown": 6,
           "Alamo Square": 11,
           "Presidio": 17,
           "Union Square": 7,
           "The Castro": 17,
           "North Beach": 8,
           "Fisherman's Wharf": 10,
           "Marina District": 11
       },
       "Presidio": {
           "Embarcadero": 20,
           "Bayview": 31,
           "Chinatown": 21,
           "Alamo Square": 19,
           "Nob Hill": 18,
           "Union Square": 22,
           "The Castro": 21,
           "North Beach": 18,
           "Fisherman's Wharf": 19,
           "Marina District": 11
       },
       "Union Square": {
           "Embarcadero": 11,
           "Bayview": 15,
           "Chinatown": 7,
           "Alamo Square": 15,
           "Nob Hill": 9,
           "Presidio": 24,
           "The Castro": 17,
           "North Beach": 10,
           "Fisherman's Wharf": 15,
           "Marina District": 18
       },
       "The Castro": {
           "Embarcadero": 22,
           "Bayview": 19,
           "Chinatown": 22,
           "Alamo Square": 8,
           "Nob Hill": 16,
           "Presidio": 20,
           "Union Square": 19,
           "North Beach": 20,
           "Fisherman's Wharf": 24,
           "Marina District": 21
       },
       "North Beach": {
           "Embarcadero": 6,
           "Bayview": 25,
           "Chinatown": 6,
           "Alamo Square": 16,
           "Nob Hill": 7,
           "Presidio": 17,
           "Union Square": 7,
           "The Castro": 23,
           "Fisherman's Wharf": 5,
           "Marina District": 9
       },
       "Fisherman's Wharf": {
           "Embarcadero": 8,
           "Bayview": 26,
           "Chinatown": 12,
           "Alamo Square": 21,
           "Nob Hill": 11,
           "Presidio": 17,
           "Union Square": 13,
           "The Castro": 27,
           "North Beach": 6,
           "Marina District": 9
       },
       "Marina District": {
           "Embarcadero": 14,
           "Bayview": 27,
           "Chinatown": 15,
           "Alamo Square": 15,
           "Nob Hill": 12,
           "Presidio": 10,
           "Union Square": 16,
           "The Castro": 22,
           "North Beach": 11,
           "Fisherman's Wharf": 10
       }
    }
    
    # Create an Optimize solver (allows optimization objectives)
    opt = Optimize()
    n = len(friends)
    
    # Decision variables for each meeting:
    # x[i]: True if meeting with friend i is scheduled.
    # order_vars[i]: an integer representing the position of the meeting in the overall sequence (0 means not scheduled).
    # s_vars[i] and e_vars[i]: start and end times (in minutes from midnight) for the meeting.
    x = [Bool(f"x_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]
    
    # For each meeting, enforce availability and duration constraints if scheduled.
    for i, friend in enumerate(friends):
        # If scheduled, order must be between 1 and n; if not, order is 0.
        opt.add(If(x[i], And(order_vars[i] >= 1, order_vars[i] <= n), order_vars[i] == 0))
        # Meeting must occur within friend's availability window.
        opt.add(Implies(x[i], s_vars[i] >= friend["avail_start"]))
        opt.add(Implies(x[i], e_vars[i] <= friend["avail_end"]))
        opt.add(Implies(x[i], e_vars[i] - s_vars[i] >= friend["duration"]))
        # If not scheduled, fix start and end times to 0.
        opt.add(Implies(Not(x[i]), s_vars[i] == 0))
        opt.add(Implies(Not(x[i]), e_vars[i] == 0))
    
    # Ensure that scheduled meetings have distinct order numbers.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(x[i], x[j]), order_vars[i] != order_vars[j]))
    
    # For any two scheduled meetings, impose travel-time and ordering constraints.
    for i in range(n):
        for j in range(n):
            if i != j:
                # If both meetings are scheduled and meeting i comes before meeting j,
                # then the start time of meeting j must be at least the end time of meeting i plus travel time.
                t_time = travel[friends[i]["location"]][friends[j]["location"]]
                opt.add(Implies(And(x[i], x[j], order_vars[i] < order_vars[j]),
                                s_vars[j] >= e_vars[i] + t_time))
    
    # For the first scheduled meeting, account for travel from the starting location "Embarcadero".
    for i in range(n):
        t_from_start = travel["Embarcadero"][friends[i]["location"]]
        opt.add(Implies(And(x[i], order_vars[i] == 1),
                        s_vars[i] >= 540 + t_from_start))
    
    # Our objective: maximize the number of scheduled meetings.
    total_meetings = Sum([If(x[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    # Check feasibility and extract model.
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(x[i])):
                order_val = model.evaluate(order_vars[i]).as_long()
                s_val = model.evaluate(s_vars[i]).as_long()
                e_val = model.evaluate(e_vars[i]).as_long()
                scheduled.append((order_val, i, s_val, e_val))
        # Sort scheduled meetings by their order in the itinerary.
        scheduled.sort(key=lambda tup: tup[0])
        
        # Helper function: convert time in minutes to 24-hour formatted string (e.g., "9:00" or "13:30").
        def format_time(t):
            hours = t // 60
            minutes = t % 60
            return f"{hours}:{minutes:02d}"
        
        itinerary = []
        for ord_val, i, s_val, e_val in scheduled:
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": format_time(s_val),
                "end_time": format_time(e_val)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()