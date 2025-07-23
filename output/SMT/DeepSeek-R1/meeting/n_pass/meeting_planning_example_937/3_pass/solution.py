import json
from z3 import *

def main():
    travel_data = """
    Russian Hill to Sunset District: 23.
    Russian Hill to Union Square: 10.
    Russian Hill to Nob Hill: 5.
    Russian Hill to Marina District: 7.
    Russian Hill to Richmond District: 14.
    Russian Hill to Financial District: 11.
    Russian Hill to Embarcadero: 8.
    Russian Hill to The Castro: 21.
    Russian Hill to Alamo Square: 15.
    Russian Hill to Presidio: 14.
    Sunset District to Russian Hill: 24.
    Sunset District to Union Square: 30.
    Sunset District to Nob Hill: 27.
    Sunset District to Marina District: 21.
    Sunset District to Richmond District: 12.
    Sunset District to Financial District: 30.
    Sunset District to Embarcadero: 30.
    Sunset District to The Castro: 17.
    Sunset District to Alamo Square: 17.
    Sunset District to Presidio: 16.
    Union Square to Russian Hill: 13.
    Union Square to Sunset District: 27.
    Union Square to Nob Hill: 9.
    Union Square to Marina District: 18.
    Union Square to Richmond District: 20.
    Union Square to Financial District: 9.
    Union Square to Embarcadero: 11.
    Union Square to The Castro: 17.
    Union Square to Alamo Square: 15.
    Union Square to Presidio: 24.
    Nob Hill to Russian Hill: 5.
    Nob Hill to Sunset District: 24.
    Nob Hill to Union Square: 7.
    Nob Hill to Marina District: 11.
    Nob Hill to Richmond District: 14.
    Nob Hill to Financial District: 9.
    Nob Hill to Embarcadero: 9.
    Nob Hill to The Castro: 17.
    Nob Hill to Alamo Square: 11.
    Nob Hill to Presidio: 17.
    Marina District to Russian Hill: 8.
    Marina District to Sunset District: 19.
    Marina District to Union Square: 16.
    Marina District to Nob Hill: 12.
    Marina District to Richmond District: 11.
    Marina District to Financial District: 17.
    Marina District to Embarcadero: 14.
    Marina District to The Castro: 22.
    Marina District to Alamo Square: 15.
    Marina District to Presidio: 10.
    Richmond District to Russian Hill: 13.
    Richmond District to Sunset District: 11.
    Richmond District to Union Square: 21.
    Richmond District to Nob Hill: 17.
    Richmond District to Marina District: 9.
    Richmond District to Financial District: 22.
    Richmond District to Embarcadero: 19.
    Richmond District to The Castro: 16.
    Richmond District to Alamo Square: 13.
    Richmond District to Presidio: 7.
    Financial District to Russian Hill: 11.
    Financial District to Sunset District: 30.
    Financial District to Union Square: 9.
    Financial District to Nob Hill: 8.
    Financial District to Marina District: 15.
    Financial District to Richmond District: 21.
    Financial District to Embarcadero: 4.
    Financial District to The Castro: 20.
    Financial District to Alamo Square: 17.
    Financial District to Presidio: 22.
    Embarcadero to Russian Hill: 8.
    Embarcadero to Sunset District: 30.
    Embarcadero to Union Square: 10.
    Embarcadero to Nob Hill: 10.
    Embarcadero to Marina District: 12.
    Embarcadero to Richmond District: 21.
    Embarcadero to Financial District: 5.
    Embarcadero to The Castro: 25.
    Embarcadero to Alamo Square: 19.
    Embarcadero to Presidio: 20.
    The Castro to Russian Hill: 18.
    The Castro to Sunset District: 17.
    The Castro to Union Square: 19.
    The Castro to Nob Hill: 16.
    The Castro to Marina District: 21.
    The Castro to Richmond District: 16.
    The Castro to Financial District: 21.
    The Castro to Embarcadero: 22.
    The Castro to Alamo Square: 8.
    The Castro to Presidio: 20.
    Alamo Square to Russian Hill: 13.
    Alamo Square to Sunset District: 16.
    Alamo Square to Union Square: 14.
    Alamo Square to Nob Hill: 11.
    Alamo Square to Marina District: 15.
    Alamo Square to Richmond District: 11.
    Alamo Square to Financial District: 17.
    Alamo Square to Embarcadero: 16.
    Alamo Square to The Castro: 8.
    Alamo Square to Presidio: 17.
    Presidio to Russian Hill: 14.
    Presidio to Sunset District: 15.
    Presidio to Union Square: 22.
    Presidio to Nob Hill: 18.
    Presidio to Marina District: 11.
    Presidio to Richmond District: 7.
    Presidio to Financial District: 23.
    Presidio to Embarcadero: 20.
    Presidio to The Castro: 21.
    Presidio to Alamo Square: 19.
    """

    travel_dict = {}
    lines = travel_data.strip().split('\n')
    for line in lines:
        parts = line.strip().split(' to ')
        if not parts or len(parts) < 2:
            continue
        from_place = parts[0].strip()
        rest = parts[1].split(':')
        if len(rest) < 2:
            continue
        to_place = rest[0].strip()
        time_str = rest[1].strip().replace('.', '')
        if time_str.isdigit():
            time_val = int(time_str)
            key = (from_place, to_place)
            travel_dict[key] = time_val

    friends = [
        {"name": "David", "location": "Sunset District", "available_start": "9:15AM", "available_end": "10:00PM", "min_duration": 15},
        {"name": "Kenneth", "location": "Union Square", "available_start": "9:15PM", "available_end": "9:45PM", "min_duration": 15},
        {"name": "Patricia", "location": "Nob Hill", "available_start": "3:00PM", "available_end": "7:15PM", "min_duration": 120},
        {"name": "Mary", "location": "Marina District", "available_start": "2:45PM", "available_end": "4:45PM", "min_duration": 45},
        {"name": "Charles", "location": "Richmond District", "available_start": "5:15PM", "available_end": "9:00PM", "min_duration": 15},
        {"name": "Joshua", "location": "Financial District", "available_start": "2:30PM", "available_end": "5:15PM", "min_duration": 90},
        {"name": "Ronald", "location": "Embarcadero", "available_start": "6:15PM", "available_end": "8:45PM", "min_duration": 30},
        {"name": "George", "location": "The Castro", "available_start": "2:15PM", "available_end": "7:00PM", "min_duration": 105},
        {"name": "Kimberly", "location": "Alamo Square", "available_start": "9:00AM", "available_end": "2:30PM", "min_duration": 105},
        {"name": "William", "location": "Presidio", "available_start": "7:00AM", "available_end": "12:45PM", "min_duration": 60}
    ]

    def time_to_minutes(time_str):
        time_str = time_str.upper()
        if time_str.endswith("AM") or time_str.endswith("PM"):
            is_pm = "PM" in time_str
            time_str = time_str.replace("AM", "").replace("PM", "").strip()
            parts = time_str.split(':')
            hour = int(parts[0])
            minute = int(parts[1]) if len(parts) > 1 else 0
            if is_pm and hour != 12:
                hour += 12
            if not is_pm and hour == 12:
                hour = 0
            return hour * 60 + minute
        return 0

    for friend in friends:
        friend["start_min"] = time_to_minutes(friend["available_start"])
        friend["end_min"] = time_to_minutes(friend["available_end"])

    n_friends = len(friends)
    travel_time_start = []
    for friend in friends:
        key = ("Russian Hill", friend["location"])
        travel_time_start.append(travel_dict[key])

    travel_time_matrix = [[0] * n_friends for _ in range(n_friends)]
    for i in range(n_friends):
        for j in range(n_friends):
            if i == j:
                travel_time_matrix[i][j] = 0
            else:
                key = (friends[i]["location"], friends[j]["location"])
                travel_time_matrix[i][j] = travel_dict.get(key, 1000)

    start_node = n_friends
    end_node = n_friends + 1
    total_nodes = n_friends + 2

    s = Solver()
    found_schedule = None
    for k in range(n_friends, 0, -1):
        s.push()
        attended = [Bool(f"attended_{i}") for i in range(n_friends)]
        s.add(Sum([If(attended[i], 1, 0) for i in range(n_friends)]) == k)
        
        next_node = [Int(f"next_{i}") for i in range(total_nodes)]
        position = [Int(f"position_{i}") for i in range(total_nodes)]
        start_time = [Int(f"start_{i}") for i in range(n_friends)]
        
        # Domain constraints
        for i in range(total_nodes):
            s.add(And(next_node[i] >= 0, next_node[i] < total_nodes))
            s.add(Or(position[i] == -1, And(position[i] >= 0, position[i] <= k+1)))
        
        # Fixed constraints for start and end
        s.add(position[start_node] == 0)
        s.add(position[end_node] == k+1)
        s.add(next_node[end_node] == end_node)
        
        if k > 0:
            s.add(And(next_node[start_node] >= 0, next_node[start_node] < n_friends))
            s.add(position[next_node[start_node]] == 1)
        else:
            s.add(next_node[start_node] == end_node)
        
        # Node constraints
        for i in range(n_friends):
            # For attended friends
            s.add(If(attended[i],
                And(
                    position[i] >= 1,
                    position[i] <= k,
                    next_node[i] != i,
                    If(next_node[i] == end_node,
                        position[i] == k,
                        And(
                            next_node[i] != end_node,
                            position[next_node[i]] == position[i] + 1
                        )
                    )
                ),
                And(
                    position[i] == -1,
                    next_node[i] == end_node
                )
            ))
        
        # Time window constraints
        for i in range(n_friends):
            s.add(Implies(attended[i], 
                          And(start_time[i] >= friends[i]["start_min"],
                              start_time[i] + friends[i]["min_duration"] <= friends[i]["end_min"])))
        
        # Travel time constraints
        for i in range(n_friends):
            s.add(Implies(And(attended[i], next_node[start_node] == i),
                          start_time[i] >= 540 + travel_time_start[i]))
            
        for i in range(n_friends):
            for j in range(n_friends):
                if i != j:
                    s.add(Implies(And(attended[i], attended[j], next_node[i] == j),
                                  start_time[j] >= start_time[i] + friends[i]["min_duration"] + travel_time_matrix[i][j]))
        
        if s.check() == sat:
            m = s.model()
            schedule = []
            current = start_node
            path = []
            while current != end_node:
                next_val = m[next_node[current]].as_long()
                if next_val < n_friends:
                    path.append(next_val)
                current = next_val
            
            for idx in path:
                if m.evaluate(attended[idx]):
                    start_val = m.evaluate(start_time[idx])
                    if isinstance(start_val, IntNumRef):
                        start_minutes = start_val.as_long()
                    else:
                        start_minutes = 0
                    end_minutes = start_minutes + friends[idx]["min_duration"]
                    start_hour = start_minutes // 60
                    start_minute = start_minutes % 60
                    end_hour = end_minutes // 60
                    end_minute = end_minutes % 60
                    schedule.append({
                        "action": "meet",
                        "person": friends[idx]["name"],
                        "start_time": f"{start_hour:02d}:{start_minute:02d}",
                        "end_time": f"{end_hour:02d}:{end_minute:02d}"
                    })
            found_schedule = schedule
            s.pop()
            break
        s.pop()

    if found_schedule is None:
        print('{"itinerary": []}')
    else:
        result = {"itinerary": found_schedule}
        print(json.dumps(result))

if __name__ == "__main__":
    main()