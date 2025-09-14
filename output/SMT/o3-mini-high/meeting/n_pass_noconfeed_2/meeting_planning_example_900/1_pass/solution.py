import json
from z3 import Optimize, Int, If, Or, And, Implies

def format_time(t):
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define friend meeting data:
    # Times are in minutes from midnight.
    friends = [
        {"name": "Matthew",   "location": "The Castro",      "avail_start": 990,  "avail_end": 1200, "min_duration": 45},
        {"name": "Rebecca",   "location": "Nob Hill",        "avail_start": 915,  "avail_end": 1155, "min_duration": 105},
        {"name": "Brian",     "location": "Marina District", "avail_start": 855,  "avail_end": 1320, "min_duration": 30},
        {"name": "Emily",     "location": "Pacific Heights", "avail_start": 675,  "avail_end": 1185, "min_duration": 15},
        {"name": "Karen",     "location": "Haight-Ashbury",  "avail_start": 705,  "avail_end": 1050, "min_duration": 30},
        {"name": "Stephanie", "location": "Mission District","avail_start": 780,  "avail_end": 945,  "min_duration": 75},
        {"name": "James",     "location": "Chinatown",       "avail_start": 870,  "avail_end": 1140, "min_duration": 120},
        {"name": "Steven",    "location": "Russian Hill",    "avail_start": 840,  "avail_end": 1200, "min_duration": 30},
        {"name": "Elizabeth", "location": "Alamo Square",    "avail_start": 780,  "avail_end": 1035, "min_duration": 120},
        {"name": "William",   "location": "Bayview",         "avail_start": 1095, "avail_end": 1215, "min_duration": 90}
    ]
    
    # Define travel times between locations (in minutes, directed)
    travel_times = {
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Russian Hill'): 13,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Bayview'): 27,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Chinatown'): 22,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Bayview'): 19,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Bayview'): 27,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Bayview'): 22,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Bayview'): 14,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Mission District'): 17,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Bayview'): 20,
        ('Russian Hill', 'Richmond District'): 14,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Bayview'): 23,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Bayview'): 16,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'The Castro'): 19,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
    }
    
    # Maximum number of meeting slots equals the number of friends.
    n_slots = len(friends)
    
    # Create an Optimize instance.
    opt = Optimize()
    
    # For each meeting slot, we choose a friend index or -1 (unused).
    slot_friends = [Int(f"slot_{i}_friend") for i in range(n_slots)]
    # Meeting start and end times (in minutes from midnight) for each slot.
    slot_start = [Int(f"slot_{i}_start") for i in range(n_slots)]
    slot_end = [Int(f"slot_{i}_end") for i in range(n_slots)]
    
    # Domain: each slot_friends variable is either -1 (unused) or an index 0..n_slots-1.
    for i in range(n_slots):
        opt.add(Or(slot_friends[i] == -1, And(slot_friends[i] >= 0, slot_friends[i] < n_slots)))
    
    # If a slot is unused, all subsequent slots must be unused.
    for i in range(n_slots - 1):
        opt.add(Implies(slot_friends[i] == -1, slot_friends[i+1] == -1))
    
    # Uniqueness: no friend is scheduled more than once.
    for i in range(n_slots):
        for j in range(i + 1, n_slots):
            opt.add(Implies(And(slot_friends[i] != -1, slot_friends[j] != -1),
                            slot_friends[i] != slot_friends[j]))
    
    # For each slot used, add constraints based on the assigned friend's availability.
    for i in range(n_slots):
        for k, f in enumerate(friends):
            # If this slot is assigned to friend k then:
            # - The meeting must start no earlier than the friend's available start.
            opt.add(Implies(slot_friends[i] == k,
                            slot_start[i] >= f["avail_start"]))
            # - The meeting must end by the friend's available end.
            opt.add(Implies(slot_friends[i] == k,
                            slot_end[i] <= f["avail_end"]))
            # - The meeting duration must be at least the required minimum.
            opt.add(Implies(slot_friends[i] == k,
                            slot_end[i] - slot_start[i] >= f["min_duration"]))
            # For the first meeting, include travel time from the starting location.
            if i == 0:
                # Arrival at Richmond District at 9:00 AM = 540 minutes.
                travel_from_start = 540 + travel_times[("Richmond District", f["location"])]
                opt.add(Implies(slot_friends[i] == k,
                                slot_start[i] >= travel_from_start))
    
    # Add travel time constraints between consecutive meetings.
    for i in range(1, n_slots):
        for k, prev_f in enumerate(friends):
            for l, curr_f in enumerate(friends):
                # If slot (i-1) is friend k and slot i is friend l then
                # meeting i must start after meeting (i-1) ends plus travel time.
                travel_time = travel_times[(prev_f["location"], curr_f["location"])]
                opt.add(Implies(And(slot_friends[i-1] == k, slot_friends[i] == l),
                                slot_start[i] >= slot_end[i-1] + travel_time))
    
    # For unused slots, fix start and end times to 0.
    for i in range(n_slots):
        opt.add(Implies(slot_friends[i] == -1, And(slot_start[i] == 0, slot_end[i] == 0)))
    
    # Objective: maximize the number of meetings scheduled.
    meeting_count = Sum([If(slot_friends[i] == -1, 0, 1) for i in range(n_slots)])
    opt.maximize(meeting_count)
    
    if opt.check() == "sat":
        model = opt.model()
        itinerary = []
        for i in range(n_slots):
            friend_idx = model.evaluate(slot_friends[i]).as_long()
            if friend_idx == -1:
                break
            start_val = model.evaluate(slot_start[i]).as_long()
            end_val = model.evaluate(slot_end[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[friend_idx]["location"],
                "person": friends[friend_idx]["name"],
                "start_time": format_time(start_val),
                "end_time": format_time(end_val)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()