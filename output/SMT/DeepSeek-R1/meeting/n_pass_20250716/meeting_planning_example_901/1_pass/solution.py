from z3 import *

def main():
    # Define the travel times as a multi-line string
    travel_text = """Russian Hill to Pacific Heights: 7.
Russian Hill to North Beach: 5.
Russian Hill to Golden Gate Park: 21.
Russian Hill to Embarcadero: 8.
Russian Hill to Haight-Ashbury: 17.
Russian Hill to Fisherman's Wharf: 7.
Russian Hill to Mission District: 16.
Russian Hill to Alamo Square: 15.
Russian Hill to Bayview: 23.
Russian Hill to Richmond District: 14.
Pacific Heights to Russian Hill: 7.
Pacific Heights to North Beach: 9.
Pacific Heights to Golden Gate Park: 15.
Pacific Heights to Embarcadero: 10.
Pacific Heights to Haight-Ashbury: 11.
Pacific Heights to Fisherman's Wharf: 13.
Pacific Heights to Mission District: 15.
Pacific Heights to Alamo Square: 10.
Pacific Heights to Bayview: 22.
Pacific Heights to Richmond District: 12.
North Beach to Russian Hill: 4.
North Beach to Pacific Heights: 8.
North Beach to Golden Gate Park: 22.
North Beach to Embarcadero: 6.
North Beach to Haight-Ashbury: 18.
North Beach to Fisherman's Wharf: 5.
North Beach to Mission District: 18.
North Beach to Alamo Square: 16.
North Beach to Bayview: 25.
North Beach to Richmond District: 18.
Golden Gate Park to Russian Hill: 19.
Golden Gate Park to Pacific Heights: 16.
Golden Gate Park to North Beach: 23.
Golden Gate Park to Embarcadero: 25.
Golden Gate Park to Haight-Ashbury: 7.
Golden Gate Park to Fisherman's Wharf: 24.
Golden Gate Park to Mission District: 17.
Golden Gate Park to Alamo Square: 9.
Golden Gate Park to Bayview: 23.
Golden Gate Park to Richmond District: 7.
Embarcadero to Russian Hill: 8.
Embarcadero to Pacific Heights: 11.
Embarcadero to North Beach: 5.
Embarcadero to Golden Gate Park: 25.
Embarcadero to Haight-Ashbury: 21.
Embarcadero to Fisherman's Wharf: 6.
Embarcadero to Mission District: 20.
Embarcadero to Alamo Square: 19.
Embarcadero to Bayview: 21.
Embarcadero to Richmond District: 21.
Haight-Ashbury to Russian Hill: 17.
Haight-Ashbury to Pacific Heights: 12.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Golden Gate Park: 7.
Haight-Ashbury to Embarcadero: 20.
Haight-Ashbury to Fisherman's Wharf: 23.
Haight-Ashbury to Mission District: 11.
Haight-Ashbury to Alamo Square: 5.
Haight-Ashbury to Bayview: 18.
Haight-Ashbury to Richmond District: 10.
Fisherman's Wharf to Russian Hill: 7.
Fisherman's Wharf to Pacific Heights: 12.
Fisherman's Wharf to North Beach: 6.
Fisherman's Wharf to Golden Gate Park: 25.
Fisherman's Wharf to Embarcadero: 8.
Fisherman's Wharf to Haight-Ashbury: 22.
Fisherman's Wharf to Mission District: 22.
Fisherman's Wharf to Alamo Square: 21.
Fisherman's Wharf to Bayview: 26.
Fisherman's Wharf to Richmond District: 18.
Mission District to Russian Hill: 15.
Mission District to Pacific Heights: 16.
Mission District to North Beach: 17.
Mission District to Golden Gate Park: 17.
Mission District to Embarcadero: 19.
Mission District to Haight-Ashbury: 12.
Mission District to Fisherman's Wharf: 22.
Mission District to Alamo Square: 11.
Mission District to Bayview: 14.
Mission District to Richmond District: 20.
Alamo Square to Russian Hill: 13.
Alamo Square to Pacific Heights: 10.
Alamo Square to North Beach: 15.
Alamo Square to Golden Gate Park: 9.
Alamo Square to Embarcadero: 16.
Alamo Square to Haight-Ashbury: 5.
Alamo Square to Fisherman's Wharf: 19.
Alamo Square to Mission District: 10.
Alamo Square to Bayview: 16.
Alamo Square to Richmond District: 11.
Bayview to Russian Hill: 23.
Bayview to Pacific Heights: 23.
Bayview to North Beach: 22.
Bayview to Golden Gate Park: 22.
Bayview to Embarcadero: 19.
Bayview to Haight-Ashbury: 19.
Bayview to Fisherman's Wharf: 25.
Bayview to Mission District: 13.
Bayview to Alamo Square: 16.
Bayview to Richmond District: 25.
Richmond District to Russian Hill: 13.
Richmond District to Pacific Heights: 10.
Richmond District to North Beach: 17.
Richmond District to Golden Gate Park: 9.
Richmond District to Embarcadero: 19.
Richmond District to Haight-Ashbury: 10.
Richmond District to Fisherman's Wharf: 18.
Richmond District to Mission District: 20.
Richmond District to Alamo Square: 13.
Richmond District to Bayview: 27."""

    # Parse the travel_text into a dictionary
    travel_dict = {}
    lines = travel_text.strip().split('\n')
    for line in lines:
        if not line.strip():
            continue
        parts = line.split(':')
        time_str = parts[1].strip().strip('.')
        time_val = int(time_str)
        loc_str = parts[0].strip()
        loc_parts = loc_str.split(' to ')
        from_loc = loc_parts[0].strip()
        to_loc = loc_parts[1].strip()
        travel_dict[(from_loc, to_loc)] = time_val

    # Define real friends with their details (times in minutes from midnight)
    real_friends = [
        {'name': 'Emily', 'location': 'Pacific Heights', 'start_win': 555, 'end_win': 825, 'min_time': 120},  # 9:15AM to 1:45PM
        {'name': 'Helen', 'location': 'North Beach', 'start_win': 825, 'end_win': 1125, 'min_time': 30},      # 1:45PM to 6:45PM
        {'name': 'Kimberly', 'location': 'Golden Gate Park', 'start_win': 1125, 'end_win': 1275, 'min_time': 75}, # 6:45PM to 9:15PM
        {'name': 'James', 'location': 'Embarcadero', 'start_win': 630, 'end_win': 690, 'min_time': 30},       # 10:30AM to 11:30AM
        {'name': 'Linda', 'location': 'Haight-Ashbury', 'start_win': 450, 'end_win': 1155, 'min_time': 15},   # 7:30AM to 7:15PM
        {'name': 'Paul', 'location': 'Fisherman\'s Wharf', 'start_win': 885, 'end_win': 1125, 'min_time': 90}, # 2:45PM to 6:45PM
        {'name': 'Anthony', 'location': 'Mission District', 'start_win': 480, 'end_win': 885, 'min_time': 105}, # 8:00AM to 2:45PM
        {'name': 'Nancy', 'location': 'Alamo Square', 'start_win': 510, 'end_win': 825, 'min_time': 120},     # 8:30AM to 1:45PM
        {'name': 'William', 'location': 'Bayview', 'start_win': 1050, 'end_win': 1230, 'min_time': 120},      # 5:30PM to 8:30PM
        {'name': 'Margaret', 'location': 'Richmond District', 'start_win': 915, 'end_win': 1095, 'min_time': 45}  # 3:15PM to 6:15PM
    ]

    # Create a dummy friend for the start at Russian Hill at 9:00AM (540 minutes from midnight)
    dummy_friend = {'name': 'start', 'location': 'Russian Hill', 'start_win': 540, 'end_win': 540, 'min_time': 0}
    friends_list = [dummy_friend] + real_friends

    # Create the solver
    s = Solver()

    # Create variables: meet and start for each friend
    meet_vars = {}
    start_vars = {}
    for friend in friends_list:
        name = friend['name']
        meet_vars[name] = Bool(f"meet_{name}")
        start_vars[name] = Int(f"start_{name}")

    # Fix the dummy friend
    s.add(meet_vars['start'] == True)
    s.add(start_vars['start'] == 540)

    # For each friend, add constraints if they are met
    for friend in friends_list:
        name = friend['name']
        start_win = friend['start_win']
        end_win = friend['end_win']
        min_time = friend['min_time']
        s.add(Implies(meet_vars[name], 
                      And(start_vars[name] >= start_win,
                          start_vars[name] + min_time <= end_win)))

    # Create order variables and constraints for every pair of friends (i < j)
    n = len(friends_list)
    order_vars = {}
    for i in range(n):
        for j in range(i+1, n):
            friend_i = friends_list[i]
            friend_j = friends_list[j]
            name_i = friend_i['name']
            name_j = friend_j['name']
            loc_i = friend_i['location']
            loc_j = friend_j['location']
            min_time_i = friend_i['min_time']
            min_time_j = friend_j['min_time']

            # Create a Bool variable for the order: True means i before j
            b = Bool(f"order_{name_i}_{name_j}")
            order_vars[(i, j)] = b

            # Constraint: if both are met, then either i before j or j before i
            s.add(Implies(And(meet_vars[name_i], meet_vars[name_j]),
                          Or(
                              And(b, start_vars[name_j] >= start_vars[name_i] + min_time_i + travel_dict[(loc_i, loc_j)]),
                              And(Not(b), start_vars[name_i] >= start_vars[name_j] + min_time_j + travel_dict[(loc_j, loc_i)])
                          )))

    # Objective: maximize the number of real friends met
    objective = Sum([If(meet_vars[friend['name']], 1, 0) for friend in real_friends])
    s.maximize(objective)

    # Check and get the model
    if s.check() == sat:
        model = s.model()
        print("SOLUTION:")
        total_met = 0
        schedule = []
        for friend in real_friends:
            name = friend['name']
            if model.evaluate(meet_vars[name]):
                total_met += 1
                start_val = model.evaluate(start_vars[name])
                # Convert start_val to integer
                if isinstance(start_val, IntNumRef):
                    start_min = start_val.as_long()
                else:
                    start_min = start_val
                hours = start_min // 60
                minutes = start_min % 60
                start_time = f"{hours:02d}:{minutes:02d}"
                end_min = start_min + friend['min_time']
                hours_end = end_min // 60
                minutes_end = end_min % 60
                end_time = f"{hours_end:02d}:{minutes_end:02d}"
                schedule.append((name, friend['location'], start_time, end_time))
        print(f"Total friends met: {total_met}")
        for entry in schedule:
            print(f"Meet {entry[0]} at {entry[1]} from {entry[2]} to {entry[3]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()