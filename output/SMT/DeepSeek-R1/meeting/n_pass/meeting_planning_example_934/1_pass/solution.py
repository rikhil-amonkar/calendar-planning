from z3 import *
import re

def main():
    n_meetings = 10
    start_node = 10
    end_node = 11

    locations = [
        "Embarcadero",    #0 Mary
        "The Castro",      #1 Kenneth
        "Haight-Ashbury", #2 Joseph
        "Union Square",    #3 Sarah
        "North Beach",     #4 Thomas
        "Pacific Heights", #5 Daniel
        "Chinatown",       #6 Richard
        "Golden Gate Park",#7 Mark
        "Marina District", #8 David
        "Russian Hill"     #9 Karen
    ]
    names = ["Mary", "Kenneth", "Joseph", "Sarah", "Thomas", "Daniel", "Richard", "Mark", "David", "Karen"]

    min_durations = [75, 30, 120, 90, 15, 15, 30, 120, 60, 120]  # in minutes

    # Available times in minutes from midnight
    available_start = [
        20 * 60,        # Mary: 20:00
        11 * 60 + 15,   # Kenneth: 11:15
        20 * 60,        # Joseph: 20:00
        11 * 60 + 45,   # Sarah: 11:45
        19 * 60 + 15,   # Thomas: 19:15
        13 * 60 + 45,   # Daniel: 13:45
        8 * 60,         # Richard: 8:00
        17 * 60 + 30,   # Mark: 17:30
        20 * 60,        # David: 20:00
        13 * 60 + 15    # Karen: 13:15
    ]
    available_end = [
        21 * 60 + 15,   # Mary: 21:15
        19 * 60 + 15,   # Kenneth: 19:15
        22 * 60,        # Joseph: 22:00
        14 * 60 + 30,   # Sarah: 14:30
        19 * 60 + 45,   # Thomas: 19:45
        20 * 60 + 30,   # Daniel: 20:30
        18 * 60 + 45,   # Richard: 18:45
        21 * 60 + 30,   # Mark: 21:30
        21 * 60,        # David: 21:00
        18 * 60 + 30    # Karen: 18:30
    ]

    travel_text = """
Nob Hill to Embarcadero: 9.
Nob Hill to The Castro: 17.
Nob Hill to Haight-Ashbury: 13.
Nob Hill to Union Square: 7.
Nob Hill to North Beach: 8.
Nob Hill to Pacific Heights: 8.
Nob Hill to Chinatown: 6.
Nob Hill to Golden Gate Park: 17.
Nob Hill to Marina District: 11.
Nob Hill to Russian Hill: 5.
Embarcadero to Nob Hill: 10.
Embarcadero to The Castro: 25.
Embarcadero to Haight-Ashbury: 21.
Embarcadero to Union Square: 10.
Embarcadero to North Beach: 5.
Embarcadero to Pacific Heights: 11.
Embarcadero to Chinatown: 7.
Embarcadero to Golden Gate Park: 25.
Embarcadero to Marina District: 12.
Embarcadero to Russian Hill: 8.
The Castro to Nob Hill: 16.
The Castro to Embarcadero: 22.
The Castro to Haight-Ashbury: 6.
The Castro to Union Square: 19.
The Castro to North Beach: 20.
The Castro to Pacific Heights: 16.
The Castro to Chinatown: 22.
The Castro to Golden Gate Park: 11.
The Castro to Marina District: 21.
The Castro to Russian Hill: 18.
Haight-Ashbury to Nob Hill: 15.
Haight-Ashbury to Embarcadero: 20.
Haight-Ashbury to The Castro: 6.
Haight-Ashbury to Union Square: 19.
Haight-Ashbury to North Beach: 19.
Haight-Ashbury to Pacific Heights: 12.
Haight-Ashbury to Chinatown: 19.
Haight-Ashbury to Golden Gate Park: 7.
Haight-Ashbury to Marina District: 17.
Haight-Ashbury to Russian Hill: 17.
Union Square to Nob Hill: 9.
Union Square to Embarcadero: 11.
Union Square to The Castro: 17.
Union Square to Haight-Ashbury: 18.
Union Square to North Beach: 10.
Union Square to Pacific Heights: 15.
Union Square to Chinatown: 7.
Union Square to Golden Gate Park: 22.
Union Square to Marina District: 18.
Union Square to Russian Hill: 13.
North Beach to Nob Hill: 7.
North Beach to Embarcadero: 6.
North Beach to The Castro: 23.
North Beach to Haight-Ashbury: 18.
North Beach to Union Square: 7.
North Beach to Pacific Heights: 8.
North Beach to Chinatown: 6.
North Beach to Golden Gate Park: 22.
North Beach to Marina District: 9.
North Beach to Russian Hill: 4.
Pacific Heights to Nob Hill: 8.
Pacific Heights to Embarcadero: 10.
Pacific Heights to The Castro: 16.
Pacific Heights to Haight-Ashbury: 11.
Pacific Heights to Union Square: 12.
Pacific Heights to North Beach: 9.
Pacific Heights to Chinatown: 11.
Pacific Heights to Golden Gate Park: 15.
Pacific Heights to Marina District: 6.
Pacific Heights to Russian Hill: 7.
Chinatown to Nob Hill: 9.
Chinatown to Embarcadero: 5.
Chinatown to The Castro: 22.
Chinatown to Haight-Ashbury: 19.
Chinatown to Union Square: 7.
Chinatown to North Beach: 3.
Chinatown to Pacific Heights: 10.
Chinatown to Golden Gate Park: 23.
Chinatown to Marina District: 12.
Chinatown to Russian Hill: 7.
Golden Gate Park to Nob Hill: 20.
Golden Gate Park to Embarcadero: 25.
Golden Gate Park to The Castro: 13.
Golden Gate Park to Haight-Ashbury: 7.
Golden Gate Park to Union Square: 22.
Golden Gate Park to North Beach: 23.
Golden Gate Park to Pacific Heights: 16.
Golden Gate Park to Chinatown: 23.
Golden Gate Park to Marina District: 16.
Golden Gate Park to Russian Hill: 19.
Marina District to Nob Hill: 12.
Marina District to Embarcadero: 14.
Marina District to The Castro: 22.
Marina District to Haight-Ashbury: 16.
Marina District to Union Square: 16.
Marina District to North Beach: 11.
Marina District to Pacific Heights: 7.
Marina District to Chinatown: 15.
Marina District to Golden Gate Park: 18.
Marina District to Russian Hill: 8.
Russian Hill to Nob Hill: 5.
Russian Hill to Embarcadero: 8.
Russian Hill to The Castro: 21.
Russian Hill to Haight-Ashbury: 17.
Russian Hill to Union Square: 10.
Russian Hill to North Beach: 5.
Russian Hill to Pacific Heights: 7.
Russian Hill to Chinatown: 9.
Russian Hill to Golden Gate Park: 21.
Russian Hill to Marina District: 7.
    """

    travel_dict = {}
    lines = travel_text.strip().split('\n')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        parts = line.split(' to ')
        if len(parts) < 2:
            continue
        from_loc = parts[0].strip()
        rest = parts[1].strip()
        if rest.find(':') == -1:
            continue
        to_loc_part, time_part = rest.split(':', 1)
        to_loc = to_loc_part.strip()
        time_str = time_part.replace('.', '').strip()
        try:
            time_val = int(time_str)
            travel_dict[(from_loc, to_loc)] = time_val
        except:
            continue

    # Add travel time for the same location as 0? Not needed, but for safety, but we avoid self-loop.
    # Also, add travel time to end_node is 0, handled in get_travel_time.

    def get_travel_time(i, j):
        if j == end_node:
            return 0
        if i == start_node:
            from_loc = "Nob Hill"
            to_loc = locations[j]
            return travel_dict.get((from_loc, to_loc), 10000)  # large number if not found
        elif i in range(n_meetings):
            from_loc = locations[i]
            if j == end_node:
                return 0
            else:
                to_loc = locations[j]
                return travel_dict.get((from_loc, to_loc), 10000)
        else:
            return 0

    s = Solver()
    opt = Optimize()

    m = [Bool('m_%d' % i) for i in range(n_meetings)]
    b = [[Bool('b_%d_%d' % (i, j)) for j in range(12)] for i in range(12)]
    t = [Int('t_%d' % i) for i in range(12)]

    # Fix start time at 9:00 AM (540 minutes from midnight)
    s.add(t[start_node] == 540)

    total_meetings = Sum([If(m_i, 1, 0) for m_i in m])

    # Start node out-degree constraint: one edge to either a meeting or the end node
    s.add(Sum([If(b[start_node][j], 1, 0) for j in list(range(n_meetings)) + [end_node]]) == 1)
    s.add(b[start_node][end_node] == (total_meetings == 0))

    # End node in-degree constraint: one incoming edge from a meeting node if at least one meeting, else 0
    s.add(Sum([If(b[i][end_node], 1, 0) for i in range(n_meetings)]) == If(total_meetings > 0, 1, 0))

    # For each meeting node
    for i in range(n_meetings):
        # In-degree: from start_node or other meetings
        in_edges = [b[j][i] for j in [start_node] + list(range(n_meetings))]
        s.add(Sum([If(edge, 1, 0) for edge in in_edges]) == If(m[i], 1, 0))

        # Out-degree: to other meetings or end_node
        out_edges = [b[i][j] for j in list(range(n_meetings)) + [end_node]]
        s.add(Sum([If(edge, 1, 0) for edge in out_edges]) == If(m[i], 1, 0))

        # Availability constraints
        s.add(Implies(m[i], t[i] >= available_start[i]))
        s.add(Implies(m[i], t[i] + min_durations[i] <= available_end[i]))

    # Edge time constraints
    for i in [start_node] + list(range(n_meetings)):
        for j in list(range(n_meetings)) + [end_node]:
            if i == j:
                s.add(b[i][j] == False)
                continue
            if j != end_node:
                duration_i = 0 if i == start_node else min_durations[i]
                tt = get_travel_time(i, j)
                s.add(Implies(b[i][j], t[j] >= t[i] + duration_i + tt))

    # No self edges and no edges from end_node
    for i in range(12):
        s.add(b[i][i] == False)
    for j in range(12):
        s.add(b[end_node][j] == False)

    opt.add(s.assertions())
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        # Extract the meetings that are scheduled
        scheduled_meetings = []
        for i in range(n_meetings):
            if is_true(model.eval(m[i])):
                start_val = model.eval(t[i]).as_long()
                end_val = start_val + min_durations[i]
                # Convert to HH:MM
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                scheduled_meetings.append({
                    'person': names[i],
                    'start_time': start_str,
                    'end_time': end_str
                })
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        itinerary = [{"action": "meet", "person": meet['person'], "start_time": meet['start_time'], "end_time": meet['end_time']} for meet in scheduled_meetings]
        result = {'itinerary': itinerary}
        print(f"SOLUTION: {result}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()