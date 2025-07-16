from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    # Define variables for each meeting's start and end times
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')
    
    daniel_start = Int('daniel_start')
    daniel_end = Int('daniel_end')
    
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')
    
    stephanie_start = Int('stephanie_start')
    stephanie_end = Int('stephanie_end')

    # Arrival at Sunset District at 9:00AM (540 minutes since midnight)
    arrival_time = 540

    # Define meeting durations in minutes
    margaret_duration = 30
    daniel_duration = 15
    charles_duration = 90
    stephanie_duration = 90

    # Define travel times from Sunset District (minutes)
    travel_to_margaret = 24  # Sunset to Russian Hill
    travel_to_daniel = 11    # Sunset to Golden Gate Park
    travel_to_charles = 17   # Sunset to Alamo Square
    travel_to_stephanie = 24 # Sunset to Mission District

    # Define travel times between locations (minutes)
    # From Golden Gate Park to Russian Hill
    daniel_to_margaret = 19
    # From Russian Hill to Alamo Square
    margaret_to_charles = 15
    # From Alamo Square to Mission District
    charles_to_stephanie = 10

    # Constraints for each friend's availability
    # Margaret: Russian Hill (9:00AM-4:00PM)
    s.add(margaret_start >= 540)  # 9:00AM
    s.add(margaret_end <= 960)    # 4:00PM
    s.add(margaret_end == margaret_start + margaret_duration)

    # Daniel: Golden Gate Park (8:00AM-1:30PM)
    s.add(daniel_start >= 480)    # 8:00AM
    s.add(daniel_end <= 810)      # 1:30PM
    s.add(daniel_end == daniel_start + daniel_duration)

    # Charles: Alamo Square (6:00PM-8:45PM)
    s.add(charles_start >= 1080)  # 6:00PM
    s.add(charles_end <= 1125)    # 8:45PM
    s.add(charles_end == charles_start + charles_duration)

    # Stephanie: Mission District (8:30PM-10:00PM)
    s.add(stephanie_start >= 1230)  # 8:30PM
    s.add(stephanie_end <= 1260)    # 10:00PM
    s.add(stephanie_end == stephanie_start + stephanie_duration)

    # Define possible meeting sequences
    # We'll try two possible sequences and pick the one that works

    # Sequence 1: Daniel -> Margaret -> Charles -> Stephanie
    seq1 = And(
        daniel_start >= arrival_time + travel_to_daniel,
        margaret_start >= daniel_end + daniel_to_margaret,
        charles_start >= margaret_end + margaret_to_charles,
        stephanie_start >= charles_end + charles_to_stephanie
    )

    # Sequence 2: Margaret -> Daniel -> Charles -> Stephanie
    seq2 = And(
        margaret_start >= arrival_time + travel_to_margaret,
        daniel_start >= margaret_end + 21,  # Russian Hill to Golden Gate Park
        charles_start >= daniel_end + 9,    # Golden Gate Park to Alamo Square
        stephanie_start >= charles_end + charles_to_stephanie
    )

    # Try both sequences
    s.push()
    s.add(seq1)
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (Sequence 1):")
        print(f"1. Meet Daniel at Golden Gate Park from {format_time(m[daniel_start].as_long())} to {format_time(m[daniel_end].as_long())}")
        print(f"2. Meet Margaret at Russian Hill from {format_time(m[margaret_start].as_long())} to {format_time(m[margaret_end].as_long())}")
        print(f"3. Meet Charles at Alamo Square from {format_time(m[charles_start].as_long())} to {format_time(m[charles_end].as_long())}")
        print(f"4. Meet Stephanie at Mission District from {format_time(m[stephanie_start].as_long())} to {format_time(m[stephanie_end].as_long())}")
        return
    s.pop()

    s.push()
    s.add(seq2)
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found (Sequence 2):")
        print(f"1. Meet Margaret at Russian Hill from {format_time(m[margaret_start].as_long())} to {format_time(m[margaret_end].as_long())}")
        print(f"2. Meet Daniel at Golden Gate Park from {format_time(m[daniel_start].as_long())} to {format_time(m[daniel_end].as_long())}")
        print(f"3. Meet Charles at Alamo Square from {format_time(m[charles_start].as_long())} to {format_time(m[charles_end].as_long())}")
        print(f"4. Meet Stephanie at Mission District from {format_time(m[stephanie_start].as_long())} to {format_time(m[stephanie_end].as_long())}")
        return
    s.pop()

    print("No feasible schedule found to meet all friends.")

def format_time(minutes):
    """Convert minutes since midnight to HH:MM format"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

solve_scheduling()