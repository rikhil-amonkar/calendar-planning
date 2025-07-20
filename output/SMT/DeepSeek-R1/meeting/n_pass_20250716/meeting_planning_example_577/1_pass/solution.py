from z3 import *

def main():
    # Convert time to minutes since midnight
    data = """
    Haight-Ashbury to Russian Hill: 17.
    Haight-Ashbury to Fisherman's Wharf: 23.
    Haight-Ashbury to Nob Hill: 15.
    Haight-Ashbury to Golden Gate Park: 7.
    Haight-Ashbury to Alamo Square: 5.
    Haight-Ashbury to Pacific Heights: 12.
    Russian Hill to Haight-Ashbury: 17.
    Russian Hill to Fisherman's Wharf: 7.
    Russian Hill to Nob Hill: 5.
    Russian Hill to Golden Gate Park: 21.
    Russian Hill to Alamo Square: 15.
    Russian Hill to Pacific Heights: 7.
    Fisherman's Wharf to Haight-Ashbury: 22.
    Fisherman's Wharf to Russian Hill: 7.
    Fisherman's Wharf to Nob Hill: 11.
    Fisherman's Wharf to Golden Gate Park: 25.
    Fisherman's Wharf to Alamo Square: 20.
    Fisherman's Wharf to Pacific Heights: 12.
    Nob Hill to Haight-Ashbury: 13.
    Nob Hill to Russian Hill: 5.
    Nob Hill to Fisherman's Wharf: 11.
    Nob Hill to Golden Gate Park: 17.
    Nob Hill to Alamo Square: 11.
    Nob Hill to Pacific Heights: 8.
    Golden Gate Park to Haight-Ashbury: 7.
    Golden Gate Park to Russian Hill: 19.
    Golden Gate Park to Fisherman's Wharf: 24.
    Golden Gate Park to Nob Hill: 20.
    Golden Gate Park to Alamo Square: 10.
    Golden Gate Park to Pacific Heights: 16.
    Alamo Square to Haight-Ashbury: 5.
    Alamo Square to Russian Hill: 13.
    Alamo Square to Fisherman's Wharf: 19.
    Alamo Square to Nob Hill: 11.
    Alamo Square to Golden Gate Park: 9.
    Alamo Square to Pacific Heights: 10.
    Pacific Heights to Haight-Ashbury: 11.
    Pacific Heights to Russian Hill: 7.
    Pacific Heights to Fisherman's Wharf: 13.
    Pacific Heights to Nob Hill: 8.
    Pacific Heights to Golden Gate Park: 15.
    Pacific Heights to Alamo Square: 10.
    """
    travel_dict = {}
    lines = data.strip().split('\n')
    for line in lines:
        parts = line.strip().split(':')
        if len(parts) < 2:
            continue
        time_val = int(parts[1].strip().rstrip('.'))
        locs = parts[0].split(' to ')
        src = locs[0].strip()
        dst = locs[1].strip()
        if src not in travel_dict:
            travel_dict[src] = {}
        travel_dict[src][dst] = time_val

    locations = [
        "Haight-Ashbury",
        "Russian Hill",
        "Fisherman's Wharf",
        "Nob Hill",
        "Golden Gate Park",
        "Alamo Square",
        "Pacific Heights"
    ]
    n = len(locations)
    travel_time = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                travel_time[i][j] = 0
            else:
                src = locations[i]
                dst = locations[j]
                travel_time[i][j] = travel_dict[src][dst]

    names = ["Dummy", "Stephanie", "Kevin", "Robert", "Steven", "Anthony", "Sandra"]
    available_start_min = [
        540,   # Dummy at 9:00AM (540 minutes)
        1200,  # Stephanie: 8:00PM (1200 minutes)
        1155,  # Kevin: 7:15PM (1155 minutes)
        465,   # Robert: 7:45AM (465 minutes)
        510,   # Steven: 8:30AM (510 minutes)
        465,   # Anthony: 7:45AM (465 minutes)
        885    # Sandra: 2:45PM (885 minutes)
    ]
    available_end_min = [
        540,   # Dummy: 9:00AM (540 minutes)
        1245,  # Stephanie: 8:45PM (1245 minutes)
        1305,  # Kevin: 9:45PM (1305 minutes)
        630,   # Robert: 10:30AM (630 minutes)
        1020,  # Steven: 5:00PM (1020 minutes)
        1185,  # Anthony: 7:45PM (1185 minutes)
        1305   # Sandra: 9:45PM (1305 minutes)
    ]
    min_duration_min = [
        0,   # Dummy
        15,  # Stephanie
        75,  # Kevin
        90,  # Robert
        75,  # Steven
        15,  # Anthony
        45   # Sandra
    ]

    s = Optimize()

    meet = [Bool(f"meet_{i}") for i in range(1, 7)]
    t = [Int(f"t_{i}") for i in range(7)]

    s.add(t[0] == 540)

    for i in range(1, 7):
        s.add(Implies(meet[i-1], t[i] >= available_start_min[i]))
        s.add(Implies(meet[i-1], t[i] + min_duration_min[i] <= available_end_min[i]))
        s.add(Implies(meet[i-1], t[i] >= 540 + travel_time[0][i]))

    for i in range(7):
        for j in range(7):
            if i == j:
                continue
            if i == 0:
                cond_i = True
            else:
                cond_i = meet[i-1]
            if j == 0:
                cond_j = True
            else:
                cond_j = meet[j-1]
            both_met = And(cond_i, cond_j)
            disj = Or(
                t[j] >= t[i] + min_duration_min[i] + travel_time[i][j],
                t[i] >= t[j] + min_duration_min[j] + travel_time[j][i]
            )
            s.add(Implies(both_met, disj))

    total_meet = Sum([If(m, 1, 0) for m in meet])
    s.maximize(total_meet)

    if s.check() == sat:
        m = s.model()
        total_friends = m.evaluate(total_meet).as_long()
        print(f"SOLUTION: We can meet {total_friends} friends.")
        for i in range(1, 7):
            meet_i_val = m.evaluate(meet[i-1])
            if meet_i_val:
                start_val = m.evaluate(t[i]).as_long()
                hours = start_val // 60
                minutes = start_val % 60
                am_pm = "AM" if hours < 12 else "PM"
                hours12 = hours % 12
                if hours12 == 0:
                    hours12 = 12
                start_str = f"{hours12}:{minutes:02d}{am_pm}"

                end_val = start_val + min_duration_min[i]
                hours_end = end_val // 60
                minutes_end = end_val % 60
                am_pm_end = "AM" if hours_end < 12 else "PM"
                hours12_end = hours_end % 12
                if hours12_end == 0:
                    hours12_end = 12
                end_str = f"{hours12_end}:{minutes_end:02d}{am_pm_end}"

                print(f"Meet {names[i]} at {locations[i]} from {start_str} to {end_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()