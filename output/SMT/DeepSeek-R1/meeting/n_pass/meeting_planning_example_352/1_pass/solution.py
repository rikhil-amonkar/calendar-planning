from z3 import *
import itertools
import json

def min_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    location = {
        'Sandra': 'Chinatown',
        'Nancy': 'Marina District',
        'Joseph': 'Haight-Ashbury',
        'Karen': 'Nob Hill'
    }
    
    travel_time_dict = {
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Marina District'): 18,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Marina District'): 11,
        ('Haight-Ashbury', 'Union Square'): 17,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Nob Hill'): 8,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Marina District'): 12,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Chinatown'): 16
    }
    
    availability_start = {
        'Sandra': 7*60+15,   # 7:15 AM = 435 minutes
        'Nancy': 11*60,       # 11:00 AM = 660 minutes
        'Joseph': 12*60+30,   # 12:30 PM = 750 minutes
        'Karen': 21*60+15     # 9:15 PM = 1275 minutes
    }
    
    availability_end = {
        'Sandra': 19*60+15,   # 7:15 PM = 1155 minutes
        'Nancy': 20*60+15,    # 8:15 PM = 1215 minutes
        'Joseph': 19*60+45,   # 7:45 PM = 1185 minutes
        'Karen': 21*60+45     # 9:45 PM = 1305 minutes
    }
    
    duration = {
        'Sandra': 75,
        'Nancy': 105,
        'Joseph': 90,
        'Karen': 30
    }
    
    start_time_union = 540  # 9:00 AM in minutes

    def check_permutation(perm):
        n = len(perm)
        s = [Int(f's_{i}') for i in range(n)]
        e = [Int(f'e_{i}') for i in range(n)]
        solver = Solver()
        
        for i in range(n):
            if perm[i] == 'Karen':
                solver.add(s[i] == availability_start['Karen'])
                solver.add(e[i] == availability_start['Karen'] + duration['Karen'])
        
        for i in range(n):
            if i == 0:
                from_place = 'Union Square'
                to_place = location[perm[0]]
                tt = travel_time_dict[(from_place, to_place)]
                base_val = start_time_union + tt
                if perm[0] == 'Karen':
                    pass
                else:
                    solver.add(s[0] >= base_val)
                    solver.add(s[0] >= availability_start[perm[0]])
                    solver.add(e[0] == s[0] + duration[perm[0]])
            else:
                from_place = location[perm[i-1]]
                to_place = location[perm[i]]
                tt = travel_time_dict[(from_place, to_place)]
                arrival_time = e[i-1] + tt
                if perm[i] == 'Karen':
                    solver.add(arrival_time <= s[i])
                else:
                    solver.add(s[i] >= arrival_time)
                    solver.add(s[i] >= availability_start[perm[i]])
                    solver.add(e[i] == s[i] + duration[perm[i]])
        
        for i in range(n):
            if perm[i] != 'Karen':
                solver.add(e[i] <= availability_end[perm[i]])
        
        if solver.check() == sat:
            model = solver.model()
            schedule = []
            for i in range(n):
                s_val = model.eval(s[i]).as_long()
                e_val = model.eval(e[i]).as_long()
                schedule.append((perm[i], s_val, e_val))
            return schedule
        else:
            return None

    friends_all = ['Sandra', 'Nancy', 'Joseph', 'Karen']
    found_schedule = None
    found_perm = None
    num_friends = 0

    for num in range(4, 0, -1):
        if found_schedule is not None:
            break
        for subset in itertools.combinations(friends_all, num):
            if found_schedule is not None:
                break
            perms = list(itertools.permutations(subset))
            for perm in perms:
                schedule = check_permutation(perm)
                if schedule is not None:
                    found_schedule = schedule
                    found_perm = perm
                    num_friends = num
                    break

    if found_schedule is None:
        print('No feasible schedule found.')
        return
    
    itinerary = []
    for meeting in found_schedule:
        person, start_min, end_min = meeting
        itinerary.append({
            "action": "meet",
            "person": person,
            "start_time": min_to_time(start_min),
            "end_time": min_to_time(end_min)
        })
    
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == '__main__':
    main()