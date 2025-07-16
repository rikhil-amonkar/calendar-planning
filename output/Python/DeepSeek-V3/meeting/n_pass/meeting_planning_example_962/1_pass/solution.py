import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_travel_time(from_loc, to_loc):
    travel_times = {
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Golden Gate Park'): 11,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Financial District'): 21,
        ('The Castro', 'Sunset District'): 17,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Sunset District'): 19,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Marina District'): 11,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Haight-Ashbury'): 15,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Financial District'): 23,
        ('Presidio', 'Sunset District'): 15,
        ('North Beach', 'The Castro'): 23,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Sunset District'): 27,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Golden Gate Park'): 25,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Sunset District'): 30,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Presidio'): 15,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'North Beach'): 23,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Alamo Square'): 9,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Sunset District'): 11,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Sunset District'): 16,
        ('Financial District', 'The Castro'): 20,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Sunset District'): 30,
        ('Sunset District', 'The Castro'): 17,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Presidio'): 16,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Embarcadero'): 30,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Financial District'): 30,
    }
    return travel_times.get((from_loc, to_loc), 0)

def main():
    friends = [
        {"name": "Elizabeth", "location": "Marina District", "start": "19:00", "end": "20:45", "min_duration": 105},
        {"name": "Joshua", "location": "Presidio", "start": "8:30", "end": "13:15", "min_duration": 105},
        {"name": "Timothy", "location": "North Beach", "start": "19:45", "end": "22:00", "min_duration": 90},
        {"name": "David", "location": "Embarcadero", "start": "10:45", "end": "12:30", "min_duration": 30},
        {"name": "Kimberly", "location": "Haight-Ashbury", "start": "16:45", "end": "21:30", "min_duration": 75},
        {"name": "Lisa", "location": "Golden Gate Park", "start": "17:30", "end": "21:45", "min_duration": 45},
        {"name": "Ronald", "location": "Richmond District", "start": "8:00", "end": "9:30", "min_duration": 90},
        {"name": "Stephanie", "location": "Alamo Square", "start": "15:30", "end": "16:30", "min_duration": 30},
        {"name": "Helen", "location": "Financial District", "start": "17:30", "end": "18:30", "min_duration": 45},
        {"name": "Laura", "location": "Sunset District", "start": "17:45", "end": "21:15", "min_duration": 90}
    ]

    current_time = time_to_minutes("9:00")
    current_location = "The Castro"
    itinerary = []

    # Priority: Ronald (must meet first)
    ronald = next(f for f in friends if f["name"] == "Ronald")
    travel_time = get_travel_time(current_location, ronald["location"])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(ronald["start"]))
    end_time = min(start_time + ronald["min_duration"], time_to_minutes(ronald["end"]))
    if end_time - start_time >= ronald["min_duration"]:
        itinerary.append({
            "action": "meet",
            "location": ronald["location"],
            "person": ronald["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = ronald["location"]

    # Next: Joshua
    joshua = next(f for f in friends if f["name"] == "Joshua")
    travel_time = get_travel_time(current_location, joshua["location"])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(joshua["start"]))
    end_time = min(start_time + joshua["min_duration"], time_to_minutes(joshua["end"]))
    if end_time - start_time >= joshua["min_duration"]:
        itinerary.append({
            "action": "meet",
            "location": joshua["location"],
            "person": joshua["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = joshua["location"]

    # Next: David
    david = next(f for f in friends if f["name"] == "David")
    travel_time = get_travel_time(current_location, david["location"])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(david["start"]))
    end_time = min(start_time + david["min_duration"], time_to_minutes(david["end"]))
    if end_time - start_time >= david["min_duration"]:
        itinerary.append({
            "action": "meet",
            "location": david["location"],
            "person": david["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = david["location"]

    # Next: Stephanie
    stephanie = next(f for f in friends if f["name"] == "Stephanie")
    travel_time = get_travel_time(current_location, stephanie["location"])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(stephanie["start"]))
    end_time = min(start_time + stephanie["min_duration"], time_to_minutes(stephanie["end"]))
    if end_time - start_time >= stephanie["min_duration"]:
        itinerary.append({
            "action": "meet",
            "location": stephanie["location"],
            "person": stephanie["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = stephanie["location"]

    # Next: Helen
    helen = next(f for f in friends if f["name"] == "Helen")
    travel_time = get_travel_time(current_location, helen["location"])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(helen["start"]))
    end_time = min(start_time + helen["min_duration"], time_to_minutes(helen["end"]))
    if end_time - start_time >= helen["min_duration"]:
        itinerary.append({
            "action": "meet",
            "location": helen["location"],
            "person": helen["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = helen["location"]

    # Next: Kimberly
    kimberly = next(f for f in friends if f["name"] == "Kimberly")
    travel_time = get_travel_time(current_location, kimberly["location"])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(kimberly["start"]))
    end_time = min(start_time + kimberly["min_duration"], time_to_minutes(kimberly["end"]))
    if end_time - start_time >= kimberly["min_duration"]:
        itinerary.append({
            "action": "meet",
            "location": kimberly["location"],
            "person": kimberly["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = kimberly["location"]

    # Next: Lisa
    lisa = next(f for f in friends if f["name"] == "Lisa")
    travel_time = get_travel_time(current_location, lisa["location"])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(lisa["start"]))
    end_time = min(start_time + lisa["min_duration"], time_to_minutes(lisa["end"]))
    if end_time - start_time >= lisa["min_duration"]:
        itinerary.append({
            "action": "meet",
            "location": lisa["location"],
            "person": lisa["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = lisa["location"]

    # Next: Laura
    laura = next(f for f in friends if f["name"] == "Laura")
    travel_time = get_travel_time(current_location, laura["location"])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(laura["start"]))
    end_time = min(start_time + laura["min_duration"], time_to_minutes(laura["end"]))
    if end_time - start_time >= laura["min_duration"]:
        itinerary.append({
            "action": "meet",
            "location": laura["location"],
            "person": laura["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = laura["location"]

    # Next: Elizabeth
    elizabeth = next(f for f in friends if f["name"] == "Elizabeth")
    travel_time = get_travel_time(current_location, elizabeth["location"])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(elizabeth["start"]))
    end_time = min(start_time + elizabeth["min_duration"], time_to_minutes(elizabeth["end"]))
    if end_time - start_time >= elizabeth["min_duration"]:
        itinerary.append({
            "action": "meet",
            "location": elizabeth["location"],
            "person": elizabeth["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        current_time = end_time
        current_location = elizabeth["location"]

    # Finally: Timothy
    timothy = next(f for f in friends if f["name"] == "Timothy")
    travel_time = get_travel_time(current_location, timothy["location"])
    arrival_time = current_time + travel_time
    start_time = max(arrival_time, time_to_minutes(timothy["start"]))
    end_time = min(start_time + timothy["min_duration"], time_to_minutes(timothy["end"]))
    if end_time - start_time >= timothy["min_duration"]:
        itinerary.append({
            "action": "meet",
            "location": timothy["location"],
            "person": timothy["name"],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()