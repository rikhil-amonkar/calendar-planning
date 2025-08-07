from z3 import *
import json

def main():
    travel_text = """
    Pacific Heights to Marina District: 6.
    Pacific Heights to The Castro: 16.
    Pacific Heights to Richmond District: 12.
    Pacific Heights to Alamo Square: 10.
    Pacific Heights to Financial District: 13.
    Pacific Heights to Presidio: 11.
    Pacific Heights to Mission District: 15.
    Pacific Heights to Nob Hill: 8.
    Pacific Heights to Russian Hill: 7.
    Marina District to Pacific Heights: 7.
    Marina District to The Castro: 22.
    Marina District to Richmond District: 11.
    Marina District to Alamo Square: 15.
    Marina District to Financial District: 17.
    Marina District to Presidio: 10.
    Marina District to Mission District: 20.
    Marina District to Nob Hill: 12.
    Marina District to Russian Hill: 8.
    The Castro to Pacific Heights: 16.
    The Castro to Marina District: 21.
    The Castro to Richmond District: 16.
    The Castro to Alamo Square: 8.
    The Castro to Financial District: 21.
    The Castro to Presidio: 20.
    The Castro to Mission District: 7.
    The Castro to Nob Hill: 16.
    The Castro to Russian Hill: 18.
    Richmond District to Pacific Heights: 10.
    Richmond District to Marina District: 9.
    Richmond District to The Castro: 16.
    Richmond District to Alamo Square: 13.
    Richmond District to Financial District: 22.
    Richmond District to Presidio: 7.
    Richmond District to Mission District: 20.
    Richmond District to Nob Hill: 17.
    Richmond District to Russian Hill: 13.
    Alamo Square to Pacific Heights: 10.
    Alamo Square to Marina District: 15.
    Alamo Square to The Castro: 8.
    Alamo Square to Richmond District: 11.
    Alamo Square to Financial District: 17.
    Alamo Square to Presidio: 17.
    Alamo Square to Mission District: 10.
    Alamo Square to Nob Hill: 11.
    Alamo Square to Russian Hill: 13.
    Financial District to Pacific Heights: 13.
    Financial District to Marina District: 15.
    Financial District to The Castro: 20.
    Financial District to Richmond District: 21.
    Financial District to Alamo Square: 17.
    Financial District to Presidio: 22.
    Financial District to Mission District: 17.
    Financial District to Nob Hill: 8.
    Financial District to Russian Hill: 11.
    Presidio to Pacific Heights: 11.
    Presidio to Marina District: 11.
    Presidio to The Castro: 21.
    Presidio to Richmond District: 7.
    Presidio to Alamo Square: 19.
    Presidio to Financial District: 23.
    Presidio to Mission District: 26.
    Presidio to Nob Hill: 18.
    Presidio to Russian Hill: 14.
    Mission District to Pacific Heights: 16.
    Mission District to Marina District: 19.
    Mission District to The Castro: 7.
    Mission District to Richmond District: 20.
    Mission District to Alamo Square: 11.
    Mission District to Financial District: 15.
    Mission District to Presidio: 25.
    Mission District to Nob Hill: 12.
    Mission District to Russian Hill: 15.
    Nob Hill to Pacific Heights: 8.
    Nob Hill to Marina District: 11.
    Nob Hill to The Castro: 17.
    Nob Hill to Richmond District: 14.
    Nob Hill to Alamo Square: 11.
    Nob Hill to Financial District: 9.
    Nob Hill to Presidio: 17.
    Nob Hill to Mission District: 13.
    Nob Hill to Russian Hill: 5.
    Russian Hill to Pacific Heights: 7.
    Russian Hill to Marina District: 7.
    Russian Hill to The Castro: 21.
    Russian Hill to Richmond District: 14.
    Russian Hill to Alamo Square: 15.
    Russian Hill to Financial District: 11.
    Russian Hill to Presidio: 14.
    Russian Hill to Mission District: 16.
    Russian Hill to Nob Hill: 5.
    """
    
    travel_dict = {}
    lines = travel_text.strip().split('.')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        parts = line.split(':')
        if len(parts) < 2:
            continue
        time_part = parts[1].strip()
        try:
            time_val = int(time_part)
        except:
            continue
        locs_part = parts[0].strip()
        if " to " not in locs_part:
            continue
        locs = locs_part.split(" to ")
        if len(locs) != 2:
            continue
        loc1 = locs[0].strip()
        loc2 = locs[1].strip()
        if loc1 not in travel_dict:
            travel_dict[loc1] = {}
        travel_dict[loc1][loc2] = time_val

    friends_data = [
        {'name': 'Linda', 'loc': 'Marina District', 'start_win': 18*60, 'end_win': 22*60, 'dur': 30},
        {'name': 'Kenneth', 'loc': 'The Castro', 'start_win': 14*60+45, 'end_win': 16*60+15, 'dur': 30},
        {'name': 'Kimberly', 'loc': 'Richmond District', 'start_win': 14*60+15, 'end_win': 22*60, 'dur': 30},
        {'name': 'Paul', 'loc': 'Alamo Square', 'start_win': 21*60, 'end_win': 21*60+30, 'dur': 15},
        {'name': 'Carol', 'loc': 'Financial District', 'start_win': 10*60+15, 'end_win': 12*60, 'dur': 60},
        {'name': 'Brian', 'loc': 'Presidio', 'start_win': 10*60, 'end_win': 21*60+30, 'dur': 75},
        {'name': 'Laura', 'loc': 'Mission District', 'start_win': 16*60+15, 'end_win': 20*60+30, 'dur': 30},
        {'name': 'Sandra', 'loc': 'Nob Hill', 'start_win': 9*60+15, 'end_win': 18*60+30, 'dur': 60},
        {'name': 'Karen', 'loc': 'Russian Hill', 'start_win': 18*60+30, 'end_win': 22*60, 'dur': 75},
    ]
    
    opt = Optimize()
    
    for friend in friends_data:
        name = friend['name']
        friend['meet_var'] = Bool('meet_' + name)
        friend['start_var'] = Int('start_' + name)
    
    start_location = 'Pacific Heights'
    start_time = 9 * 60
    
    for friend in friends_data:
        meet_var = friend['meet_var']
        start_var = friend['start_var']
        loc = friend['loc']
        start_win = friend['start_win']
        end_win = friend['end_win']
        dur = friend['dur']
        travel_from_start = travel_dict[start_location][loc]
        opt.add(Implies(meet_var, start_var >= start_time + travel_from_start))
        opt.add(Implies(meet_var, start_var >= start_win))
        opt.add(Implies(meet_var, start_var + dur <= end_win))
    
    n = len(friends_data)
    for i in range(n):
        for j in range(i+1, n):
            friend_i = friends_data[i]
            friend_j = friends_data[j]
            meet_i = friend_i['meet_var']
            meet_j = friend_j['meet_var']
            s_i = friend_i['start_var']
            s_j = friend_j['start_var']
            dur_i = friend_i['dur']
            dur_j = friend_j['dur']
            loc_i = friend_i['loc']
            loc_j = friend_j['loc']
            travel_ij = travel_dict[loc_i][loc_j]
            travel_ji = travel_dict[loc_j][loc_i]
            
            # Create condition that both meetings occur
            both_meet = And(meet_i, meet_j)
            # Option 1: meeting i then meeting j (with travel)
            seq1 = (s_i + dur_i + travel_ij <= s_j)
            # Option 2: meeting j then meeting i (with travel)
            seq2 = (s_j + dur_j + travel_ji <= s_i)
            # If both meetings occur, then one sequence must be satisfied
            constraint = Implies(both_meet, Or(seq1, seq2))
            opt.add(constraint)
    
    objective = Sum([If(friend['meet_var'], 1, 0) for friend in friends_data])
    opt.maximize(objective)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for friend in friends_data:
            if is_true(model[friend['meet_var']]):
                start_min = model[friend['start_var']].as_long()
                end_min = start_min + friend['dur']
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friend['name'],
                    "start_time": start_str,
                    "end_time": end_str
                })
        itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
        result = {"itinerary": itinerary_sorted}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()