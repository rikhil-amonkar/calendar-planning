from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define all times in minutes since midnight
    # Meeting duration requirements
    margaret_duration = 30  # min 30 minutes
    daniel_duration = 15    # min 15 minutes
    charles_duration = 90   # min 90 minutes
    stephanie_duration = 90 # min 90 minutes

    # Define variables for meeting start times
    m_start = Int('m_start')  # Margaret at Russian Hill
    d_start = Int('d_start')  # Daniel at Golden Gate Park
    c_start = Int('c_start')  # Charles at Alamo Square
    s_start = Int('s_start')  # Stephanie at Mission District

    # Define travel times (minutes)
    # From Sunset District to:
    to_russian_hill = 24
    to_golden_gate = 11
    to_alamo_square = 17
    to_mission_dist = 24

    # Between locations:
    golden_gate_to_russian_hill = 19
    russian_hill_to_alamo_square = 15
    alamo_square_to_mission_dist = 10

    # Arrival time at Sunset District: 9:00AM (540 minutes)
    arrival = 540

    # Friend availability windows (in minutes since midnight)
    # Margaret: 9:00AM-4:00PM (540-960)
    s.add(m_start >= 540 + to_russian_hill)
    s.add(m_start + margaret_duration <= 960)

    # Daniel: 8:00AM-1:30PM (480-810)
    s.add(d_start >= max(480, arrival + to_golden_gate))
    s.add(d_start + daniel_duration <= 810)

    # Charles: 6:00PM-8:45PM (1080-1125)
    s.add(c_start >= 1080)
    s.add(c_start + charles_duration <= 1125)

    # Stephanie: 8:30PM-10:00PM (1230-1260)
    s.add(s_start >= 1230)
    s.add(s_start + stephanie_duration <= 1260)

    # Define possible meeting sequences
    # Sequence 1: Daniel -> Margaret -> Charles -> Stephanie
    seq1 = And(
        d_start >= arrival + to_golden_gate,
        m_start >= d_start + daniel_duration + golden_gate_to_russian_hill,
        c_start >= m_start + margaret_duration + russian_hill_to_alamo_square,
        s_start >= c_start + charles_duration + alamo_square_to_mission_dist
    )

    # Sequence 2: Margaret -> Daniel -> Charles -> Stephanie
    seq2 = And(
        m_start >= arrival + to_russian_hill,
        d_start >= m_start + margaret_duration + 21,  # Russian Hill to Golden Gate Park
        c_start >= d_start + daniel_duration + 9,    # Golden Gate Park to Alamo Square
        s_start >= c_start + charles_duration + alamo_square_to_mission_dist
    )

    # Try sequence 1 first
    s.push()
    s.add(seq1)
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule Found:")
        print(f"1. Daniel at Golden Gate Park: {format_time(m[d_start].as_long())}-{format_time(m[d_start].as_long() + daniel_duration)}")
        print(f"2. Margaret at Russian Hill: {format_time(m[m_start].as_long())}-{format_time(m[m_start].as_long() + margaret_duration)}")
        print(f"3. Charles at Alamo Square: {format_time(m[c_start].as_long())}-{format_time(m[c_start].as_long() + charles_duration)}")
        print(f"4. Stephanie at Mission District: {format_time(m[s_start].as_long())}-{format_time(m[s_start].as_long() + stephanie_duration)}")
        return
    s.pop()

    # Try sequence 2 if sequence 1 fails
    s.push()
    s.add(seq2)
    if s.check() == sat:
        m = s.model()
        print("Alternative Schedule Found:")
        print(f"1. Margaret at Russian Hill: {format_time(m[m_start].as_long())}-{format_time(m[m_start].as_long() + margaret_duration)}")
        print(f"2. Daniel at Golden Gate Park: {format_time(m[d_start].as_long())}-{format_time(m[d_start].as_long() + daniel_duration)}")
        print(f"3. Charles at Alamo Square: {format_time(m[c_start].as_long())}-{format_time(m[c_start].as_long() + charles_duration)}")
        print(f"4. Stephanie at Mission District: {format_time(m[s_start].as_long())}-{format_time(m[s_start].as_long() + stephanie_duration)}")
        return
    s.pop()

    print("No feasible schedule found that meets all constraints.")

def format_time(minutes):
    """Convert minutes since midnight to HH:MM format"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solve_scheduling()