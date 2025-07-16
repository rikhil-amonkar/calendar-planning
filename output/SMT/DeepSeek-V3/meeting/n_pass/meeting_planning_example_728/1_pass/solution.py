from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define districts
    districts = ['Marina', 'Mission', 'Fisherman', 'Presidio', 'Union', 'Sunset', 'Financial', 'Haight', 'Russian']
    district_indices = {d: i for i, d in enumerate(districts)}

    # Travel times matrix (minutes)
    travel_times = [
        [0, 20, 10, 10, 16, 19, 17, 16, 8],    # Marina
        [19, 0, 22, 25, 15, 24, 15, 12, 15],     # Mission
        [9, 22, 0, 17, 13, 27, 11, 22, 7],       # Fisherman
        [11, 26, 19, 0, 22, 15, 23, 15, 14],     # Presidio
        [18, 14, 15, 24, 0, 27, 9, 18, 13],      # Union
        [21, 25, 29, 16, 30, 0, 30, 15, 24],     # Sunset
        [15, 17, 10, 22, 9, 30, 0, 19, 11],     # Financial
        [17, 11, 23, 15, 19, 15, 21, 0, 17],    # Haight
        [7, 16, 7, 14, 10, 23, 11, 17, 0]        # Russian
    ]

    # Friends data: name, district, start_available, end_available, min_duration (minutes)
    friends = [
        ('Karen', 'Mission', 14*60 + 15, 22*60, 30),
        ('Richard', 'Fisherman', 14*60 + 30, 17*60 + 30, 30),
        ('Robert', 'Presidio', 21*60 + 45, 22*60 + 45, 60),
        ('Joseph', 'Union', 11*60 + 45, 14*60 + 45, 120),
        ('Helen', 'Sunset', 14*60 + 45, 20*60 + 45, 105),
        ('Elizabeth', 'Financial', 10*60, 12*60 + 45, 75),
        ('Kimberly', 'Haight', 14*60 + 15, 17*60 + 30, 105),
        ('Ashley', 'Russian', 11*60 + 30, 21*60 + 30, 45)
    ]

    # Current location starts at Marina at 9:00 AM (540 minutes)
    current_time = 540
    current_district = district_indices['Marina']

    # Variables for each meeting: start, end, and district
    meetings = []
    for i, (name, district, start_avail, end_avail, min_dur) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        district_idx = district_indices[district]
        meetings.append((name, start, end, district_idx, start_avail, end_avail, min_dur))
        s.add(start >= start_avail)
        s.add(end <= end_avail)
        s.add(end == start + min_dur)

    # Ensure meetings don't overlap and account for travel time
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            m1_name, m1_start, m1_end, m1_dist, _, _, _ = meetings[i]
            m2_name, m2_start, m2_end, m2_dist, _, _, _ = meetings[j]
            # Either m1 is before m2 plus travel time, or vice versa
            s.add(Or(
                m1_end + travel_times[m1_dist][m2_dist] <= m2_start,
                m2_end + travel_times[m2_dist][m1_dist] <= m1_start
            ))

    # First meeting must be after current time plus travel time
    for i in range(len(meetings)):
        _, m_start, _, m_dist, _, _, _ = meetings[i]
        s.add(m_start >= current_time + travel_times[current_district][m_dist])

    # Try to maximize the number of meetings (soft constraint)
    # In this case, we want to meet all friends, so we don't need to maximize
    # But we can add constraints to ensure all meetings are scheduled

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for name, start, end, district, _, _, _ in meetings:
            start_val = m.evaluate(start).as_long()
            end_val = m.evaluate(end).as_long()
            scheduled_meetings.append((name, start_val, end_val, districts[district]))
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: x[1])
        
        # Print schedule
        print("SOLUTION:")
        for name, start, end, district in scheduled_meetings:
            start_hr = start // 60
            start_min = start % 60
            end_hr = end // 60
            end_min = end % 60
            print(f"Meet {name} at {district} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No valid schedule found.")

solve_scheduling()