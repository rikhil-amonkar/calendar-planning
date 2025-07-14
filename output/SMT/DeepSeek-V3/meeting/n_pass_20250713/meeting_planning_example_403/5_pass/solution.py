from z3 import *

def solve_scheduling():
    s = Solver()

    # Locations mapping
    locations = {
        'Union Square': 0,
        'Golden Gate Park': 1,
        'Pacific Heights': 2,
        'Presidio': 3,
        'Chinatown': 4,
        'The Castro': 5
    }

    # Travel times matrix (minutes)
    travel = [
        [0, 22, 15, 24, 7, 19],
        [22, 0, 16, 11, 23, 13],
        [15, 16, 0, 11, 11, 16],
        [24, 11, 11, 0, 21, 21],
        [7, 23, 10, 19, 0, 20],
        [19, 11, 16, 20, 20, 0]
    ]

    # Friend data: name, location, start, end, min duration (minutes from 9:00AM)
    friends = [
        ('Robert', 5, 8*60+30, 14*60+15, 30),
        ('Rebecca', 4, 9*60+45, 21*60+30, 90),
        ('Andrew', 1, 11*60+45, 14*60+30, 75),
        ('Sarah', 2, 16*60+15, 18*60+45, 15),
        ('Nancy', 3, 17*60+30, 19*60+15, 60)
    ]

    # Variables for start and end times
    starts = [Int(f'start_{name}') for name,_,_,_,_ in friends]
    ends = [Int(f'end_{name}') for name,_,_,_,_ in friends]

    # Meeting constraints
    for i, (name, loc, f_start, f_end, min_dur) in enumerate(friends):
        s.add(starts[i] >= f_start)
        s.add(ends[i] <= f_end)
        s.add(ends[i] - starts[i] >= min_dur)
        s.add(starts[i] >= 0)
        s.add(ends[i] >= 0)

    # Initial position at Union Square at 9:00AM (time=0)
    current_time = 0
    current_loc = locations['Union Square']

    # Meeting order: Robert -> Rebecca -> Andrew -> Sarah -> Nancy
    for i in range(len(friends)):
        s.add(starts[i] >= current_time + travel[current_loc][friends[i][1]])
        current_time = ends[i]
        current_loc = friends[i][1]

    # No overlapping meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            s.add(Or(ends[i] + travel[friends[i][1]][friends[j][1]] <= starts[j],
                     ends[j] + travel[friends[j][1]][friends[i][1]] <= starts[i]))

    if s.check() == sat:
        m = s.model()
        print("Feasible Schedule Found:")
        print("Starting at Union Square at 9:00AM")
        
        current_time = 0
        current_loc = locations['Union Square']
        
        for i, (name, loc, _, _, _) in enumerate(friends):
            start = m.evaluate(starts[i]).as_long()
            end = m.evaluate(ends[i]).as_long()
            travel_time = travel[current_loc][loc]
            
            print(f"\nTravel from {list(locations.keys())[current_loc]} to {list(locations.keys())[loc]}: {travel_time} mins")
            print(f"Meet {name} at {list(locations.keys())[loc]}:")
            print(f"  Start: {start//60:02d}:{start%60:02d}")
            print(f"  End: {end//60:02d}:{end%60:02d}")
            print(f"  Duration: {end-start} minutes")
            
            current_time = end
            current_loc = loc
        
        print("\nAll 5 friends successfully scheduled!")
    else:
        print("No feasible schedule found (this shouldn't happen with these constraints)")

solve_scheduling()