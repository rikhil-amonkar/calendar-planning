from z3 import *
import json

def main():
    friends = ["Matthew", "Rebecca", "Brian", "Emily", "Karen", "Stephanie", "James", "Steven", "Elizabeth", "William"]
    locations = {
        "Matthew": "The Castro",
        "Rebecca": "Nob Hill",
        "Brian": "Marina District",
        "Emily": "Pacific Heights",
        "Karen": "Haight-Ashbury",
        "Stephanie": "Mission District",
        "James": "Chinatown",
        "Steven": "Russian Hill",
        "Elizabeth": "Alamo Square",
        "William": "Bayview"
    }

    availability_start = {
        "Matthew": 450,   # 4:30PM
        "Rebecca": 375,   # 3:15PM
        "Brian": 315,     # 2:15PM
        "Emily": 135,     # 11:15AM
        "Karen": 165,     # 11:45AM
        "Stephanie": 240, # 1:00PM
        "James": 330,     # 2:30PM
        "Steven": 300,    # 2:00PM
        "Elizabeth": 240, # 1:00PM
        "William": 555    # 6:15PM
    }
    availability_end = {
        "Matthew": 660,   # 8:00PM
        "Rebecca": 615,   # 7:15PM
        "Brian": 780,     # 10:00PM
        "Emily": 645,     # 7:45PM
        "Karen": 510,     # 5:30PM
        "Stephanie": 405, # 3:45PM
        "James": 600,     # 7:00PM
        "Steven": 660,    # 8:00PM
        "Elizabeth": 495, # 5:15PM
        "William": 675    # 8:15PM
    }

    min_durations = {
        "Matthew": 45,
        "Rebecca": 105,
        "Brian": 30,
        "Emily": 15,
        "Karen": 30,
        "Stephanie": 75,
        "James": 120,
        "Steven": 30,
        "Elizabeth": 120,
        "William": 90
    }

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
        ('Bayview', 'Alamo Square'): 16
    }

    k_values = [10,9,8,7,6,5,4,3,2,1]
    schedule_found = None

    for k in k_values:
        s = Solver()
        s.set("timeout", 30000)  # 30 seconds timeout per k

        meet_vars = {name: Bool(f"meet_{name}_{k}") for name in friends}
        start_vars = {name: Int(f"start_{name}_{k}") for name in friends}
        end_vars = {name: Int(f"end_{name}_{k}") for name in friends}
        order_vars = {name: Int(f"order_{name}_{k}") for name in friends}

        s.add(PbEq([(meet_vars[name], 1) for name in friends], k))

        for name in friends:
            s.add(If(meet_vars[name],
                    And(order_vars[name] >= 0, order_vars[name] < k),
                    order_vars[name] == -1))

        s.add(Distinct([order_vars[name] for name in friends]))

        for name in friends:
            s.add(If(meet_vars[name],
                    And(
                        start_vars[name] >= availability_start[name],
                        end_vars[name] == start_vars[name] + min_durations[name],
                        end_vars[name] <= availability_end[name]
                    ),
                    True))

        for name in friends:
            loc = locations[name]
            travel_time = travel_times[('Richmond District', loc)]
            s.add(If(And(meet_vars[name], order_vars[name] == 0),
                    start_vars[name] >= travel_time,
                    True))

        for name_i in friends:
            for name_j in friends:
                if name_i == name_j:
                    continue
                loc_i = locations[name_i]
                loc_j = locations[name_j]
                travel_time = travel_times[(loc_i, loc_j)]
                s.add(If(And(meet_vars[name_i], meet_vars[name_j], 
                             order_vars[name_j] == order_vars[name_i] + 1),
                         start_vars[name_j] >= end_vars[name_i] + travel_time,
                         True))

        result = s.check()
        if result == sat:
            model = s.model()
            schedule = []
            for name in friends:
                if model.eval(meet_vars[name]):
                    start_val = model.eval(start_vars[name]).as_long()
                    end_val = model.eval(end_vars[name]).as_long()
                    total_minutes_start = 540 + start_val
                    hour_start = total_minutes_start // 60
                    minute_start = total_minutes_start % 60
                    total_minutes_end = 540 + end_val
                    hour_end = total_minutes_end // 60
                    minute_end = total_minutes_end % 60
                    start_str = f"{hour_start:02d}:{minute_start:02d}"
                    end_str = f"{hour_end:02d}:{minute_end:02d}"
                    schedule.append({
                        "action": "meet",
                        "person": name,
                        "start_time": start_str,
                        "end_time": end_str
                    })
            schedule.sort(key=lambda x: x['start_time'])
            schedule_found = schedule
            break
        elif result == unknown:
            continue
        else:
            continue

    if schedule_found is not None:
        result = {"itinerary": schedule_found}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()