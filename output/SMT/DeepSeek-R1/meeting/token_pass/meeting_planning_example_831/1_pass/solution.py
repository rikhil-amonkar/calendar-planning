from z3 import *
import json

def main():
    # Convert time to minutes since 9:00 AM
    def time_to_minutes(t):
        hours, minutes = map(int, t.split(':'))
        return (hours - 9) * 60 + minutes

    def minutes_to_time(m):
        total_minutes = int(m)
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"

    # Travel times dictionary
    travel_times = {
        "Presidio": {
            "Fisherman's Wharf": 19,
            "Alamo Square": 19,
            "Financial District": 23,
            "Union Square": 22,
            "Sunset District": 15,
            "Embarcadero": 20,
            "Golden Gate Park": 12,
            "Chinatown": 21,
            "Richmond District": 7
        },
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Alamo Square": 21,
            "Financial District": 11,
            "Union Square": 13,
            "Sunset District": 27,
            "Embarcadero": 8,
            "Golden Gate Park": 25,
            "Chinatown": 12,
            "Richmond District": 18
        },
        "Alamo Square": {
            "Presidio": 17,
            "Fisherman's Wharf": 19,
            "Financial District": 17,
            "Union Square": 14,
            "Sunset District": 16,
            "Embarcadero": 16,
            "Golden Gate Park": 9,
            "Chinatown": 15,
            "Richmond District": 11
        },
        "Financial District": {
            "Presidio": 22,
            "Fisherman's Wharf": 10,
            "Alamo Square": 17,
            "Union Square": 9,
            "Sunset District": 30,
            "Embarcadero": 4,
            "Golden Gate Park": 23,
            "Chinatown": 5,
            "Richmond District": 21
        },
        "Union Square": {
            "Presidio": 24,
            "Fisherman's Wharf": 15,
            "Alamo Square": 15,
            "Financial District": 9,
            "Sunset District": 27,
            "Embarcadero": 11,
            "Golden Gate Park": 22,
            "Chinatown": 7,
            "Richmond District": 20
        },
        "Sunset District": {
            "Presidio": 16,
            "Fisherman's Wharf": 29,
            "Alamo Square": 17,
            "Financial District": 30,
            "Union Square": 30,
            "Embarcadero": 30,
            "Golden Gate Park": 11,
            "Chinatown": 30,
            "Richmond District": 12
        },
        "Embarcadero": {
            "Presidio": 20,
            "Fisherman's Wharf": 6,
            "Alamo Square": 19,
            "Financial District": 5,
            "Union Square": 10,
            "Sunset District": 30,
            "Golden Gate Park": 25,
            "Chinatown": 7,
            "Richmond District": 21
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Fisherman's Wharf": 24,
            "Alamo Square": 9,
            "Financial District": 26,
            "Union Square": 22,
            "Sunset District": 10,
            "Embarcadero": 25,
            "Chinatown": 23,
            "Richmond District": 7
        },
        "Chinatown": {
            "Presidio": 19,
            "Fisherman's Wharf": 8,
            "Alamo Square": 17,
            "Financial District": 5,
            "Union Square": 7,
            "Sunset District": 29,
            "Embarcadero": 5,
            "Golden Gate Park": 23,
            "Richmond District": 20
        },
        "Richmond District": {
            "Presidio": 7,
            "Fisherman's Wharf": 18,
            "Alamo Square": 13,
            "Financial District": 22,
            "Union Square": 21,
            "Sunset District": 11,
            "Embarcadero": 19,
            "Golden Gate Park": 9,
            "Chinatown": 20
        }
    }

    # Friends data: name, location, available start, available end, minimum duration
    friends_data = [
        ("Jeffrey", "Fisherman's Wharf", "10:15", "13:00", 90),
        ("Ronald", "Alamo Square", "7:45", "14:45", 120),
        ("Jason", "Financial District", "10:45", "16:00", 105),
        ("Melissa", "Union Square", "17:45", "18:15", 15),
        ("Elizabeth", "Sunset District", "14:45", "17:30", 105),
        ("Margaret", "Embarcadero", "13:15", "19:00", 90),
        ("George", "Golden Gate Park", "19:00", "22:00", 75),
        ("Richard", "Chinatown", "9:30", "21:00", 15),
        ("Laura", "Richmond District", "9:45", "18:00", 60)
    ]

    # Convert times to minutes
    friends = []
    for name, loc, start, end, dur in friends_data:
        start_min = time_to_minutes(start)
        end_min = time_to_minutes(end)
        # Adjust for early availability (Ronald at 7:45 which is before 9:00)
        start_min = max(0, start_min)
        friends.append((name, loc, start_min, end_min, dur))

    # Initialize Z3 solver
    s = Optimize()

    # Meeting variables: whether we meet each friend, and start time
    meet_vars = [Bool(f"meet_{i}") for i in range(len(friends))]
    start_vars = [Int(f"start_{i}") for i in range(len(friends))]

    # Constraints for each friend
    for i, (name, loc, start_avail, end_avail, dur) in enumerate(friends):
        s.add(Implies(meet_vars[i], start_vars[i] >= start_avail))
        s.add(Implies(meet_vars[i], start_vars[i] + dur <= end_avail))

    # Travel constraints between meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # If both meetings are scheduled, ensure travel time between them
                constraint = Implies(And(meet_vars[i], meet_vars[j]),
                                    Or(
                                        start_vars[j] >= start_vars[i] + dur_i + travel_times[loc_i][loc_j],
                                        start_vars[i] >= start_vars[j] + dur_j + travel_times[loc_j][loc_i]
                                    ))
                s.add(constraint)

    # Travel from Presidio to first meeting
    for i in range(len(friends)):
        name, loc, start_avail, end_avail, dur = friends[i]
        travel_from_presidio = travel_times["Presidio"][loc]
        s.add(Implies(meet_vars[i], start_vars[i] >= travel_from_presidio))

    # Maximize the number of meetings
    s.maximize(Sum([If(meet_vars[i], 1, 0) for i in range(len(friends))]))

    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i, (name, loc, _, _, dur) in enumerate(friends):
            if is_true(model.eval(meet_vars[i])):
                start_val = model.eval(start_vars[i]).as_long()
                start_time = minutes_to_time(start_val)
                end_time = minutes_to_time(start_val + dur)
                itinerary.append({
                    "action": "meet",
                    "location": loc,
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()