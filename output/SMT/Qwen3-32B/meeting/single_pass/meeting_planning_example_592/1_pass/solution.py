import itertools
import json
from z3 import *

def solve_scheduling():
    friends_list = ['Sandra', 'Jeffrey', 'Mark', 'Robert', 'Carol', 'James']
    friends = {
        'Sandra': {'location': 'Nob Hill', 'start': 480, 'end': 930, 'duration': 15},
        'Jeffrey': {'location': 'Union Square', 'start': 570, 'end': 930, 'duration': 120},
        'Mark': {'location': 'Golden Gate Park', 'start': 690, 'end': 1065, 'duration': 15},
        'Robert': {'location': 'Chinatown', 'start': 735, 'end': 1005, 'duration': 90},
        'Carol': {'location': 'Mission District', 'start': 1095, 'end': 1275, 'duration': 15},
        'James': {'location': 'Pacific Heights', 'start': 1200, 'end': 1320, 'duration': 120}
    }
    travel_times = {
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Nob Hill'): 7,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Mission District'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Nob Hill'): 8,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Nob Hill'): 9,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Nob Hill'): 12,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Golden Gate Park'): 17,
    }

    for seq in itertools.permutations(friends_list):
        arrival = {}
        start = {}
        end = {}
        for friend in seq:
            arrival[friend] = Int(f'arrival_{friend}')
            start[friend] = Int(f'start_{friend}')
            end[friend] = Int(f'end_{friend}')
        s = Solver()
        prev_end = 540  # 9:00 AM in minutes
        for i, friend in enumerate(seq):
            if i == 0:
                prev_loc = 'North Beach'
            else:
                prev_loc = friends[seq[i-1]]['location']
            curr_loc = friends[friend]['location']
            travel_key = (prev_loc, curr_loc)
            if travel_key not in travel_times:
                continue  # Skip this permutation if travel time not defined
            travel_time = travel_times[travel_key]
            arrival_time = prev_end + travel_time
            s.add(arrival[friend] == arrival_time)
            s.add(start[friend] >= arrival[friend])
            s.add(start[friend] >= friends[friend]['start'])
            s.add(end[friend] == start[friend] + friends[friend]['duration'])
            s.add(end[friend] <= friends[friend]['end'])
            prev_end = end[friend]
        if s.check() == sat:
            model = s.model()
            itinerary = []
            for friend in seq:
                st = model[start[friend]].as_long()
                et = model[end[friend]].as_long()
                start_time = f"{st//60:02d}:{st%60:02d}"
                end_time = f"{et//60:02d}:{et%60:02d}"
                itinerary.append({"action": "meet", "person": friend, "start_time": start_time, "end_time": end_time})
            return json.dumps({"itinerary": itinerary})
    return json.dumps({"itinerary": []})

print(solve_scheduling())