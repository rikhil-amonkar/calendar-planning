from z3 import *
import json

def main():
    friends = ['Charles', 'Robert', 'Nancy', 'Brian', 'Kimberly', 'David', 'William', 'Jeffrey', 'Karen', 'Joshua']
    
    locations = {
        'Charles': 'Presidio',
        'Robert': 'Nob Hill',
        'Nancy': 'Pacific Heights',
        'Brian': 'Mission District',
        'Kimberly': 'Marina District',
        'David': 'North Beach',
        'William': 'Russian Hill',
        'Jeffrey': 'Richmond District',
        'Karen': 'Embarcadero',
        'Joshua': 'Alamo Square'
    }
    
    available_start_minutes = {
        'Charles': 255,   # 13:15
        'Robert': 255,     # 13:15
        'Nancy': 345,      # 14:45
        'Brian': 390,      # 15:30
        'Kimberly': 480,   # 17:00
        'David': 345,      # 14:45
        'William': 210,    # 12:30
        'Jeffrey': 180,    # 12:00
        'Karen': 315,      # 14:15
        'Joshua': 585      # 18:45
    }
    
    available_end_minutes = {
        'Charles': 360,    # 15:00
        'Robert': 510,     # 17:30
        'Nancy': 780,      # 22:00
        'Brian': 780,      # 22:00
        'Kimberly': 645,   # 19:45
        'David': 450,      # 16:30
        'William': 615,    # 19:15
        'Jeffrey': 615,    # 19:15
        'Karen': 705,      # 20:45
        'Joshua': 780      # 22:00
    }
    
    min_durations = {
        'Charles': 105,
        'Robert': 90,
        'Nancy': 105,
        'Brian': 60,
        'Kimberly': 75,
        'David': 75,
        'William': 120,
        'Jeffrey': 45,
        'Karen': 60,
        'Joshua': 60
    }
    
    travel_dict = {
        'Sunset District': {
            'Presidio': 16,
            'Nob Hill': 27,
            'Pacific Heights': 21,
            'Mission District': 25,
            'Marina District': 21,
            'North Beach': 28,
            'Russian Hill': 24,
            'Richmond District': 12,
            'Embarcadero': 30,
            'Alamo Square': 17
        },
        'Presidio': {
            'Sunset District': 15,
            'Nob Hill': 18,
            'Pacific Heights': 11,
            'Mission District': 26,
            'Marina District': 11,
            'North Beach': 18,
            'Russian Hill': 14,
            'Richmond District': 7,
            'Embarcadero': 20,
            'Alamo Square': 19
        },
        'Nob Hill': {
            'Sunset District': 24,
            'Presidio': 17,
            'Pacific Heights': 8,
            'Mission District': 13,
            'Marina District': 11,
            'North Beach': 8,
            'Russian Hill': 5,
            'Richmond District': 14,
            'Embarcadero': 9,
            'Alamo Square': 11
        },
        'Pacific Heights': {
            'Sunset District': 21,
            'Presidio': 11,
            'Nob Hill': 8,
            'Mission District': 15,
            'Marina District': 6,
            'North Beach': 9,
            'Russian Hill': 7,
            'Richmond District': 12,
            'Embarcadero': 10,
            'Alamo Square': 10
        },
        'Mission District': {
            'Sunset District': 24,
            'Presidio': 25,
            'Nob Hill': 12,
            'Pacific Heights': 16,
            'Marina District': 19,
            'North Beach': 17,
            'Russian Hill': 15,
            'Richmond District': 20,
            'Embarcadero': 19,
            'Alamo Square': 11
        },
        'Marina District': {
            'Sunset District': 19,
            'Presidio': 10,
            'Nob Hill': 12,
            'Pacific Heights': 7,
            'Mission District': 20,
            'North Beach': 11,
            'Russian Hill': 8,
            'Richmond District': 11,
            'Embarcadero': 14,
            'Alamo Square': 15
        },
        'North Beach': {
            'Sunset District': 27,
            'Presidio': 17,
            'Nob Hill': 7,
            'Pacific Heights': 8,
            'Mission District': 18,
            'Marina District': 9,
            'Russian Hill': 4,
            'Richmond District': 18,
            'Embarcadero': 6,
            'Alamo Square': 16
        },
        'Russian Hill': {
            'Sunset District': 23,
            'Presidio': 14,
            'Nob Hill': 5,
            'Pacific Heights': 7,
            'Mission District': 16,
            'Marina District': 7,
            'North Beach': 5,
            'Richmond District': 14,
            'Embarcadero': 8,
            'Alamo Square': 15
        },
        'Richmond District': {
            'Sunset District': 11,
            'Presidio': 7,
            'Nob Hill': 17,
            'Pacific Heights': 10,
            'Mission District': 20,
            'Marina District': 9,
            'North Beach': 17,
            'Russian Hill': 13,
            'Embarcadero': 19,
            'Alamo Square': 13
        },
        'Embarcadero': {
            'Sunset District': 30,
            'Presidio': 20,
            'Nob Hill': 10,
            'Pacific Heights': 11,
            'Mission District': 20,
            'Marina District': 12,
            'North Beach': 5,
            'Russian Hill': 8,
            'Richmond District': 21,
            'Alamo Square': 19
        },
        'Alamo Square': {
            'Sunset District': 16,
            'Presidio': 17,
            'Nob Hill': 11,
            'Pacific Heights': 10,
            'Mission District': 10,
            'Marina District': 15,
            'North Beach': 15,
            'Russian Hill': 13,
            'Richmond District': 11,
            'Embarcadero': 16
        }
    }
    
    s = Optimize()
    
    met = {friend: Bool(f'met_{friend}') for friend in friends}
    start = {friend: Int(f'start_{friend}') for friend in friends}
    
    constraints = []
    
    for friend in friends:
        loc = locations[friend]
        travel_from_sunset = travel_dict['Sunset District'][loc]
        c1 = Implies(met[friend], start[friend] >= available_start_minutes[friend])
        c2 = Implies(met[friend], start[friend] + min_durations[friend] <= available_end_minutes[friend])
        c3 = Implies(met[friend], start[friend] >= travel_from_sunset)
        constraints.append(c1)
        constraints.append(c2)
        constraints.append(c3)
    
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            friend_i = friends[i]
            friend_j = friends[j]
            loc_i = locations[friend_i]
            loc_j = locations[friend_j]
            travel_ij = travel_dict[loc_i][loc_j]
            travel_ji = travel_dict[loc_j][loc_i]
            cond = Or(
                start[friend_j] >= start[friend_i] + min_durations[friend_i] + travel_ij,
                start[friend_i] >= start[friend_j] + min_durations[friend_j] + travel_ji
            )
            c = Implies(And(met[friend_i], met[friend_j]), cond)
            constraints.append(c)
    
    s.add(constraints)
    obj = Sum([If(met[friend], 1, 0) for friend in friends])
    s.maximize(obj)
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for friend in friends:
            if m.evaluate(met[friend]):
                start_val = m.evaluate(start[friend]).as_long()
                total_minutes = start_val
                hours = 9 + total_minutes // 60
                minutes = total_minutes % 60
                start_time = f"{hours:02d}:{minutes:02d}"
                end_val = start_val + min_durations[friend]
                hours_end = 9 + end_val // 60
                minutes_end = end_val % 60
                end_time = f"{hours_end:02d}:{minutes_end:02d}"
                schedule.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": start_time,
                    "end_time": end_time
                })
        schedule.sort(key=lambda x: x['start_time'])
        result = {"itinerary": schedule}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()