import itertools
import json

def main():
    travel_time = {
        'Embarcadero': {'Presidio': 20, 'Richmond District': 21, "Fisherman's Wharf": 6},
        'Presidio': {'Embarcadero': 20, 'Richmond District': 7, "Fisherman's Wharf": 19},
        'Richmond District': {'Embarcadero': 19, 'Presidio': 7, "Fisherman's Wharf": 18},
        "Fisherman's Wharf": {'Embarcadero': 8, 'Presidio': 17, 'Richmond District': 18}
    }

    friends = ['Betty', 'David', 'Barbara']
    locations = {
        'Betty': 'Presidio',
        'David': 'Richmond District',
        'Barbara': "Fisherman's Wharf"
    }
    min_durations = {
        'Betty': 45,
        'David': 90,
        'Barbara': 120
    }
    available_start = {
        'Betty': 615,   # 10:15
        'David': 780,   # 13:00
        'Barbara': 555  # 9:15
    }
    available_end = {
        'Betty': 1290,  # 21:30
        'David': 1215,  # 20:15
        'Barbara': 1215 # 20:15
    }
    start_time_total = 540   # 9:00

    def format_time(minutes):
        hours = minutes // 60
        minutes_part = minutes % 60
        return f"{hours}:{minutes_part:02d}"

    permutations = list(itertools.permutations(friends))
    found_three = False
    three_itinerary = None
    for perm in permutations:
        current_time = start_time_total
        current_loc = 'Embarcadero'
        itinerary = []
        feasible = True
        for person in perm:
            loc = locations[person]
            if current_loc == loc:
                travel_dur = 0
            else:
                travel_dur = travel_time[current_loc][loc]
            arrival = current_time + travel_dur
            start_meeting = max(arrival, available_start[person])
            end_meeting = start_meeting + min_durations[person]
            if end_meeting > available_end[person]:
                feasible = False
                break
            itinerary.append((person, loc, start_meeting, end_meeting))
            current_time = end_meeting
            current_loc = loc
        if feasible:
            found_three = True
            three_itinerary = itinerary
            break

    if found_three:
        itinerary_json = []
        for meeting in three_itinerary:
            person, loc, start_min, end_min = meeting
            itinerary_json.append({
                "action": "meet",
                "location": loc,
                "person": person,
                "start_time": format_time(start_min),
                "end_time": format_time(end_min)
            })
        result = {"itinerary": itinerary_json}
        print(json.dumps(result))
        return

    pairs = [('Barbara','Betty'), ('Barbara','David'), ('Betty','David')]
    found_two = False
    two_itinerary = None
    for pair in pairs:
        orders = [list(pair), list(pair)[::-1]]
        for order in orders:
            current_time = start_time_total
            current_loc = 'Embarcadero'
            itinerary = []
            feasible = True
            for person in order:
                loc = locations[person]
                if current_loc == loc:
                    travel_dur = 0
                else:
                    travel_dur = travel_time[current_loc][loc]
                arrival = current_time + travel_dur
                start_meeting = max(arrival, available_start[person])
                end_meeting = start_meeting + min_durations[person]
                if end_meeting > available_end[person]:
                    feasible = False
                    break
                itinerary.append((person, loc, start_meeting, end_meeting))
                current_time = end_meeting
                current_loc = loc
            if feasible and len(itinerary) == 2:
                found_two = True
                two_itinerary = itinerary
                break
        if found_two:
            break

    if found_two:
        itinerary_json = []
        for meeting in two_itinerary:
            person, loc, start_min, end_min = meeting
            itinerary_json.append({
                "action": "meet",
                "location": loc,
                "person": person,
                "start_time": format_time(start_min),
                "end_time": format_time(end_min)
            })
        result = {"itinerary": itinerary_json}
        print(json.dumps(result))
        return

    found_one = False
    one_itinerary = None
    for person in friends:
        loc = locations[person]
        travel_dur = travel_time['Embarcadero'][loc]
        arrival = start_time_total + travel_dur
        start_meeting = max(arrival, available_start[person])
        end_meeting = start_meeting + min_durations[person]
        if end_meeting <= available_end[person]:
            found_one = True
            one_itinerary = [(person, loc, start_meeting, end_meeting)]
            break

    if found_one:
        itinerary_json = []
        for meeting in one_itinerary:
            person, loc, start_min, end_min = meeting
            itinerary_json.append({
                "action": "meet",
                "location": loc,
                "person": person,
                "start_time": format_time(start_min),
                "end_time": format_time(end_min)
            })
        result = {"itinerary": itinerary_json}
        print(json.dumps(result))
        return

    result = {"itinerary": []}
    print(json.dumps(result))

if __name__ == "__main__":
    main()