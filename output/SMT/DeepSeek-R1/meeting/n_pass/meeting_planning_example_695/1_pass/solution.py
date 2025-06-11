from z3 import *

def main():
    # Define travel times between locations
    travel_times = {
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Chinatown'): 18,
        ('Bayview', 'The Castro'): 20,
        ('Bayview', 'Presidio'): 31,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Russian Hill'): 23,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'The Castro'): 19,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Russian Hill'): 13,
        ('Chinatown', 'Bayview'): 22,
        ('Chinatown', 'Nob Hill'): 8,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Russian Hill'): 7,
        ('The Castro', 'Bayview'): 19,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Chinatown'): 20,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Russian Hill'): 18,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Russian Hill'): 14,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Union Square'): 11,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Presidio'): 14,
        ('Russian Hill', 'Pacific Heights'): 7
    }
    
    # Location indices
    loc_index = {
        'Bayview': 0,
        'Nob Hill': 1,
        'Union Square': 2,
        'Chinatown': 3,
        'The Castro': 4,
        'Presidio': 5,
        'Pacific Heights': 6,
        'Russian Hill': 7
    }
    
    # Build distance matrix
    dist = [[0]*8 for _ in range(8)]
    for (from_loc, to_loc), time in travel_times.items():
        i = loc_index[from_loc]
        j = loc_index[to_loc]
        dist[i][j] = time

    # Friend data
    friends = [
        {'name': 'Paul', 'location': 'Nob Hill', 'start_avail': 435, 'end_avail': 735, 'min_duration': 60},
        {'name': 'Carol', 'location': 'Union Square', 'start_avail': 540, 'end_avail': 675, 'min_duration': 120},
        {'name': 'Patricia', 'location': 'Chinatown', 'start_avail': 660, 'end_avail': 750, 'min_duration': 75},
        {'name': 'Karen', 'location': 'The Castro', 'start_avail': 480, 'end_avail': 600, 'min_duration': 45},
        {'name': 'Nancy', 'location': 'Presidio', 'start_avail': 165, 'end_avail': 780, 'min_duration': 30},
        {'name': 'Jeffrey', 'location': 'Pacific Heights', 'start_avail': 660, 'end_avail': 705, 'min_duration': 45},
        {'name': 'Matthew', 'location': 'Russian Hill', 'start_avail': 405, 'end_avail': 765, 'min_duration': 75}
    ]
    
    # Initialize Z3 variables
    meet = []
    start = []
    friend_loc_index = []
    start_avail_arr = []
    end_avail_arr = []
    min_duration_arr = []
    
    for friend in friends:
        meet.append(Bool(f"meet_{friend['name']}"))
        start.append(Int(f"start_{friend['name']}"))
        friend_loc_index.append(loc_index[friend['location']])
        start_avail_arr.append(friend['start_avail'])
        end_avail_arr.append(friend['end_avail'])
        min_duration_arr.append(friend['min_duration'])
    
    s = Solver()
    opt = Optimize()
    
    # Add constraints for each friend
    for i in range(7):
        s.add(Implies(meet[i], And(
            start[i] >= start_avail_arr[i],
            start[i] + min_duration_arr[i] <= end_avail_arr[i],
            start[i] >= dist[0][friend_loc_index[i]]
        )))
    
    # Add pairwise constraints for friends
    for i in range(7):
        for j in range(i+1, 7):
            cond1 = (start[i] + min_duration_arr[i] + dist[friend_loc_index[i]][friend_loc_index[j]] <= start[j])
            cond2 = (start[j] + min_duration_arr[j] + dist[friend_loc_index[j]][friend_loc_index[i]] <= start[i])
            s.add(Implies(And(meet[i], meet[j]), Or(cond1, cond2)))
    
    # Maximize the number of friends met
    obj = Sum([If(meet[i], 1, 0) for i in range(7)])
    opt.add(s.assertions())
    opt.maximize(obj)
    
    # Solve and print results
    if opt.check() == sat:
        m = opt.model()
        total_met = 0
        schedule = []
        for i in range(7):
            if m.evaluate(meet[i]):
                total_met += 1
                start_val = m.evaluate(start[i]).as_long()
                end_val = start_val + min_duration_arr[i]
                # Convert to time string
                def to_time(minutes):
                    total_min = 9*60 + minutes
                    hour = total_min // 60
                    minute = total_min % 60
                    period = "AM" if hour < 12 else "PM"
                    hour12 = hour % 12
                    if hour12 == 0:
                        hour12 = 12
                    return f"{hour12}:{minute:02d} {period}"
                start_str = to_time(start_val)
                end_str = to_time(end_val)
                schedule.append((friends[i]['name'], friends[i]['location'], start_str, end_str))
        
        print(f"Total friends met: {total_met}")
        for name, loc, s_str, e_str in schedule:
            print(f"Meet {name} at {loc} from {s_str} to {e_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()