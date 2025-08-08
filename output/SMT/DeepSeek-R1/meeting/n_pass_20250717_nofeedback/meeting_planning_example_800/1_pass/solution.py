from z3 import *

def min_to_time(minutes):
    total_minutes = minutes
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

travel_text = """
Union Square to The Castro: 17.
Union Square to North Beach: 10.
Union Square to Embarcadero: 11.
Union Square to Alamo Square: 15.
Union Square to Nob Hill: 9.
Union Square to Presidio: 24.
Union Square to Fisherman's Wharf: 15.
Union Square to Mission District: 14.
Union Square to Haight-Ashbury: 18.
The Castro to Union Square: 19.
The Castro to North Beach: 20.
The Castro to Embarcadero: 22.
The Castro to Alamo Square: 8.
The Castro to Nob Hill: 16.
The Castro to Presidio: 20.
The Castro to Fisherman's Wharf: 24.
The Castro to Mission District: 7.
The Castro to Haight-Ashbury: 6.
North Beach to Union Square: 7.
North Beach to The Castro: 23.
North Beach to Embarcadero: 6.
North Beach to Alamo Square: 16.
North Beach to Nob Hill: 7.
North Beach to Presidio: 17.
North Beach to Fisherman's Wharf: 5.
North Beach to Mission District: 18.
North Beach to Haight-Ashbury: 18.
Embarcadero to Union Square: 10.
Embarcadero to The Castro: 25.
Embarcadero to North Beach: 5.
Embarcadero to Alamo Square: 19.
Embarcadero to Nob Hill: 10.
Embarcadero to Presidio: 20.
Embarcadero to Fisherman's Wharf: 6.
Embarcadero to Mission District: 20.
Embarcadero to Haight-Ashbury: 21.
Alamo Square to Union Square: 14.
Alamo Square to The Castro: 8.
Alamo Square to North Beach: 15.
Alamo Square to Embarcadero: 16.
Alamo Square to Nob Hill: 11.
Alamo Square to Presidio: 17.
Alamo Square to Fisherman's Wharf: 19.
Alamo Square to Mission District: 10.
Alamo Square to Haight-Ashbury: 5.
Nob Hill to Union Square: 7.
Nob Hill to The Castro: 17.
Nob Hill to North Beach: 8.
Nob Hill to Embarcadero: 9.
Nob Hill to Alamo Square: 11.
Nob Hill to Presidio: 17.
Nob Hill to Fisherman's Wharf: 10.
Nob Hill to Mission District: 13.
Nob Hill to Haight-Ashbury: 13.
Presidio to Union Square: 22.
Presidio to The Castro: 21.
Presidio to North Beach: 18.
Presidio to Embarcadero: 20.
Presidio to Alamo Square: 19.
Presidio to Nob Hill: 18.
Presidio to Fisherman's Wharf: 19.
Presidio to Mission District: 26.
Presidio to Haight-Ashbury: 15.
Fisherman's Wharf to Union Square: 13.
Fisherman's Wharf to The Castro: 27.
Fisherman's Wharf to North Beach: 6.
Fisherman's Wharf to Embarcadero: 8.
Fisherman's Wharf to Alamo Square: 21.
Fisherman's Wharf to Nob Hill: 11.
Fisherman's Wharf to Presidio: 17.
Fisherman's Wharf to Mission District: 22.
Fisherman's Wharf to Haight-Ashbury: 22.
Mission District to Union Square: 15.
Mission District to The Castro: 7.
Mission District to North Beach: 17.
Mission District to Embarcadero: 19.
Mission District to Alamo Square: 11.
Mission District to Nob Hill: 12.
Mission District to Presidio: 25.
Mission District to Fisherman's Wharf: 22.
Mission District to Haight-Ashbury: 12.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to The Castro: 6.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Embarcadero: 20.
Haight-Ashbury to Alamo Square: 5.
Haight-Ashbury to Nob Hill: 15.
Haight-Ashbury to Presidio: 15.
Haight-Ashbury to Fisherman's Wharf: 23.
Haight-Ashbury to Mission District: 11.
"""

travel_time_dict = {}
lines = travel_text.strip().split('\n')
for line in lines:
    if line:
        parts = line.split(':')
        locations_str = parts[0].strip()
        time_str = parts[1].strip().rstrip('.')
        from_loc, to_loc = locations_str.split(' to ')
        travel_time_dict[(from_loc, to_loc)] = int(time_str)

friends = [
    {"name": "Melissa", "location": "The Castro", "window_start": 675, "window_end": 735, "min_duration": 30},
    {"name": "Kimberly", "location": "North Beach", "window_start": 0, "window_end": 90, "min_duration": 15},
    {"name": "Joseph", "location": "Embarcadero", "window_start": 390, "window_end": 630, "min_duration": 75},
    {"name": "Barbara", "location": "Alamo Square", "window_start": 705, "window_end": 765, "min_duration": 15},
    {"name": "Kenneth", "location": "Nob Hill", "window_start": 195, "window_end": 495, "min_duration": 105},
    {"name": "Joshua", "location": "Presidio", "window_start": 450, "window_end": 555, "min_duration": 105},
    {"name": "Brian", "location": "Fisherman's Wharf", "window_start": 30, "window_end": 390, "min_duration": 45},
    {"name": "Steven", "location": "Mission District", "window_start": 630, "window_end": 720, "min_duration": 90},
    {"name": "Betty", "location": "Haight-Ashbury", "window_start": 600, "window_end": 690, "min_duration": 90}
]

s = Solver()
meet = [Bool(f"meet_{i}") for i in range(9)]
start = [Int(f"start_{i}") for i in range(10)]
end = [Int(f"end_{i}") for i in range(10)]

s.add(start[0] == 0, end[0] == 0)

for i in range(9):
    loc = friends[i]['location']
    s.add(Implies(meet[i], 
                  And(start[i+1] >= friends[i]['window_start'],
                      end[i+1] == start[i+1] + friends[i]['min_duration'],
                      end[i+1] <= friends[i]['window_end'])))
    travel_time_first = travel_time_dict[("Union Square", loc)]
    s.add(Implies(meet[i], 
                  end[0] + travel_time_first <= start[i+1]))

for i in range(9):
    for j in range(i+1, 9):
        loc_i = friends[i]['location']
        loc_j = friends[j]['location']
        time_ij = travel_time_dict[(loc_i, loc_j)]
        time_ji = travel_time_dict[(loc_j, loc_i)]
        s.add(Implies(And(meet[i], meet[j]),
                      Or(end[i+1] + time_ij <= start[j+1],
                         end[j+1] + time_ji <= start[i+1])))

objective = Sum([If(meet[i], 1, 0) for i in range(9)])
s.maximize(objective)

if s.check() == sat:
    model = s.model()
    scheduled_meetings = []
    for i in range(9):
        if model.eval(meet[i]):
            start_val = model.eval(start[i+1]).as_long()
            end_val = model.eval(end[i+1]).as_long()
            start_time_str = min_to_time(start_val)
            end_time_str = min_to_time(end_val)
            scheduled_meetings.append({
                "action": "meet",
                "person": friends[i]['name'],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    scheduled_meetings.sort(key=lambda x: x['start_time'])
    print('SOLUTION:')
    print(f'{{"itinerary": {scheduled_meetings}}}')
else:
    print("No solution found")