from z3 import *
import json

def minutes_to_time(minutes):
    # Convert minutes (offset from 9:00) to a 24-hour formatted time string
    total = 9 * 60 + minutes  # 9:00 AM is the reference (9*60 minutes)
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an optimizer instance
    opt = Optimize()

    # Define travel times (in minutes) between locations
    # Locations: "Embarcadero", "Presidio", "Richmond District", "Fisherman's Wharf"
    travel = {
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18,
    }

    # Friends' meeting constraints:
    # Each friend is represented as a tuple: (location, available_start, available_end, min_meeting_duration)
    # Times (in minutes after 9:00 AM):
    # Betty: available from 10:15 (75) to 21:30 (750) and min duration 45 minutes.
    # David: available from 13:00 (240) to 20:15 (675) and min duration 90 minutes.
    # Barbara: available from 9:15 (15) to 20:15 (675) and min duration 120 minutes.
    friends_data = {
        "Betty": ("Presidio", 75, 750, 45),
        "David": ("Richmond District", 240, 675, 90),
        "Barbara": ("Fisherman's Wharf", 15, 675, 120),
    }

    # Create SMT variables for each friend: start time (S), end time (E), and meeting order (order)
    S = {}
    E = {}
    order = {}
    for friend, (location, avail_start, avail_end, min_duration) in friends_data.items():
        S[friend] = Int(f"S_{friend}")
        E[friend] = Int(f"E_{friend}")
        order[friend] = Int(f"order_{friend}")
        # Meeting time constraints: must occur within the friend's available window and meet duration requirements
        opt.add(S[friend] >= avail_start)
        opt.add(E[friend] <= avail_end)
        opt.add(E[friend] - S[friend] >= min_duration)
        # Ensure non-negative times
        opt.add(S[friend] >= 0)
        opt.add(E[friend] >= 0)
        # Meeting order should be one of 1, 2, or 3.
        opt.add(Or(order[friend] == 1, order[friend] == 2, order[friend] == 3))

    # Enforce that the meeting order among friends is a permutation (all orders distinct)
    opt.add(Distinct(list(order.values())))

    # For the first meeting, ensure that the meeting start time is not before travel from Embarcadero.
    for friend, (location, avail_start, avail_end, min_duration) in friends_data.items():
        travel_from_start = travel[("Embarcadero", location)]
        opt.add(Implies(order[friend] == 1, S[friend] >= travel_from_start))

    # Add ordering constraints between meetings (if friend A is scheduled before friend B,
    # then friend B's meeting must start after friend A's meeting ends plus travel time between locations)
    friends = list(friends_data.keys())
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                friend_i = friends[i]
                friend_j = friends[j]
                loc_i = friends_data[friend_i][0]
                loc_j = friends_data[friend_j][0]
                travel_time = travel[(loc_i, loc_j)]
                opt.add(Implies(order[friend_i] < order[friend_j], S[friend_j] >= E[friend_i] + travel_time))

    # Introduce an auxiliary variable representing the finishing time of the last meeting.
    T_final = Int("T_final")
    for friend in friends:
        opt.add(T_final >= E[friend])

    # Optimality objective: minimize the finishing time of the last meeting.
    opt.minimize(T_final)

    # Check for satisfiability and get an optimal model.
    if opt.check() == sat:
        model = opt.model()
        # Gather schedule information as a list of tuples: (order, friend, location, start_time, end_time)
        schedule = []
        for friend in friends:
            order_val = model.evaluate(order[friend]).as_long()
            start_val = model.evaluate(S[friend]).as_long()
            end_val = model.evaluate(E[friend]).as_long()
            location = friends_data[friend][0]
            schedule.append((order_val, friend, location, start_val, end_val))
        # Sort the schedule by meeting order.
        schedule.sort(key=lambda x: x[0])

        # Build the itinerary list with JSON format.
        itinerary = []
        for ord_val, friend, location, start_val, end_val in schedule:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })

        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        # If no valid schedule is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()