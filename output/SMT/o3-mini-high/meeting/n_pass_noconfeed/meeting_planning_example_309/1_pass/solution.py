from z3 import *
import json

def minutes_to_time_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define friend information and locations.
    # Times are in minutes after midnight.
    friend_info = {
        0: {"name": "Nancy", "location": "Chinatown", "avail_start": 570, "avail_end": 810, "min_duration": 90},          # 9:30 to 13:30
        1: {"name": "Mary", "location": "Alamo Square", "avail_start": 420, "avail_end": 1260, "min_duration": 75},       # 7:00 to 21:00
        2: {"name": "Jessica", "location": "Bayview", "avail_start": 675, "avail_end": 825, "min_duration": 45},          # 11:15 to 13:45
        3: {"name": "Rebecca", "location": "Fisherman's Wharf", "avail_start": 420, "avail_end": 510, "min_duration": 45}   # 7:00 to 8:30
    }
    
    # Define travel times (in minutes) between locations.
    travel = {
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Chinatown"): 16,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "Bayview"): 26,
    }
    
    # Our starting point and time.
    initial_location = "Financial District"
    initial_time = 540  # 9:00 AM
    
    # Number of meeting slots (we have 4 friends).
    N = 4

    # Create an Optimize object.
    opt = Optimize()

    # Decision variables:
    # friend_vars[i] is an integer: -1 indicates no meeting scheduled in slot i,
    # 0: Nancy, 1: Mary, 2: Jessica, 3: Rebecca
    friend_vars = [Int(f'friend_{i}') for i in range(N)]
    start_vars = [Int(f'start_{i}') for i in range(N)]
    end_vars = [Int(f'end_{i}') for i in range(N)]

    # Domain constraints for friend_vars: they can be -1 (empty) or 0,1,2,3.
    for i in range(N):
        opt.add(friend_vars[i] >= -1, friend_vars[i] <= 3)
        
    # If a slot is empty (friend == -1), force start and end times to 0.
    for i in range(N):
        opt.add(If(friend_vars[i] == -1, And(start_vars[i] == 0, end_vars[i] == 0), True))
    
    # Availability and duration constraints for each scheduled meeting.
    for i in range(N):
        for f in [0, 1, 2, 3]:
            info = friend_info[f]
            opt.add(Implies(friend_vars[i] == f,
                            And(
                                start_vars[i] >= info["avail_start"],
                                end_vars[i] <= info["avail_end"],
                                end_vars[i] - start_vars[i] >= info["min_duration"],
                                start_vars[i] < end_vars[i]
                            )))
    
    # Constraint: Once an empty slot is reached, all subsequent slots must be empty.
    for i in range(N - 1):
        opt.add(Implies(friend_vars[i] == -1, friend_vars[i+1] == -1))
    
    # Constraint: Each friend can only be scheduled once.
    for i in range(N):
        for j in range(i+1, N):
            opt.add(Implies(And(friend_vars[i] != -1, friend_vars[j] != -1),
                            friend_vars[i] != friend_vars[j]))

    # Define travel time expression from a given friend fprev to friend fcurr.
    def travel_between(fprev, fcurr):
        return If(fprev == 0,
                  If(fcurr == 0, 0,  # not applicable; same friend won't be scheduled
                     If(fcurr == 1, 17,
                        If(fcurr == 2, 22,
                           If(fcurr == 3, 8, 0)))),
               If(fprev == 1,
                  If(fcurr == 0, 16,
                     If(fcurr == 1, 0,
                        If(fcurr == 2, 16,
                           If(fcurr == 3, 19, 0)))),
               If(fprev == 2,
                  If(fcurr == 0, 18,
                     If(fcurr == 1, 16,
                        If(fcurr == 2, 0,
                           If(fcurr == 3, 25, 0)))),
               If(fprev == 3,
                  If(fcurr == 0, 12,
                     If(fcurr == 1, 20,
                        If(fcurr == 2, 26,
                           If(fcurr == 3, 0, 0)))),
                  0))))
    
    # Travel constraint for the first meeting slot (from initial location).
    init_travel = If(friend_vars[0] == 0, travel[(initial_location, "Chinatown")],
                  If(friend_vars[0] == 1, travel[(initial_location, "Alamo Square")],
                  If(friend_vars[0] == 2, travel[(initial_location, "Bayview")],
                  If(friend_vars[0] == 3, travel[(initial_location, "Fisherman's Wharf")], 0))))
    opt.add(Implies(friend_vars[0] != -1, start_vars[0] >= initial_time + init_travel))
    
    # Travel constraints between consecutive meeting slots.
    for i in range(1, N):
        opt.add(Implies(And(friend_vars[i-1] != -1, friend_vars[i] != -1),
                        start_vars[i] >= end_vars[i-1] + travel_between(friend_vars[i-1], friend_vars[i])))
    
    # Objective: maximize the number of meetings scheduled.
    meeting_count = Sum([If(friend_vars[i] != -1, 1, 0) for i in range(N)])
    opt.maximize(meeting_count)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(N):
            if model.evaluate(friend_vars[i]).as_long() != -1:
                f_id = model.evaluate(friend_vars[i]).as_long()
                person = friend_info[f_id]["name"]
                location = friend_info[f_id]["location"]
                start_time_val = model.evaluate(start_vars[i]).as_long()
                end_time_val = model.evaluate(end_vars[i]).as_long()
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": minutes_to_time_str(start_time_val),
                    "end_time": minutes_to_time_str(end_time_val)
                })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == '__main__':
    main()