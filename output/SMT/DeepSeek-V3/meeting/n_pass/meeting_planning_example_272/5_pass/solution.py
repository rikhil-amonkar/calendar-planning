from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting times (in minutes since 9:00 AM)
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    ashley_start = Int('ashley_start')
    ashley_end = Int('ashley_end')
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')

    # Meeting duration constraints
    s.add(timothy_end - timothy_start >= 120)  # 2 hours with Timothy
    s.add(ashley_end - ashley_start >= 45)     # 45 minutes with Ashley
    s.add(patricia_end - patricia_start >= 90) # 1.5 hours with Patricia

    # Availability windows (minutes since 9:00 AM)
    s.add(And(timothy_start >= 45, timothy_end <= 1065))    # 9:45AM-5:45PM
    s.add(And(ashley_start >= 690, ashley_end <= 735))       # 8:30PM-9:15PM
    s.add(And(patricia_start >= 570, patricia_end <= 765))   # 6:30PM-9:45PM

    # Travel times between locations (minutes)
    travel = {
        ('Russian Hill', 'Embarcadero'): 8,
        ('Embarcadero', 'Mission District'): 20,
        ('Mission District', 'Nob Hill'): 12,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Nob Hill', 'Mission District'): 13
    }

    # Try different meeting sequences

    # Sequence 1: Timothy -> Ashley -> Patricia
    seq1 = Solver()
    seq1.add(s.assertions())
    seq1.add(timothy_start >= 8)  # Travel from Russian Hill to Embarcadero
    seq1.add(ashley_start >= timothy_end + travel[('Embarcadero', 'Mission District')])
    seq1.add(patricia_start >= ashley_end + travel[('Mission District', 'Nob Hill')])
    
    if seq1.check() == sat:
        m = seq1.model()
        print("SOLUTION:")
        print(f"1. Travel from Russian Hill to Embarcadero (8 min)")
        print(f"2. Meet Timothy at Embarcadero from {mins_to_time(m[timothy_start].as_long())} to {mins_to_time(m[timothy_end].as_long())}")
        print(f"3. Travel to Mission District (20 min)")
        print(f"4. Meet Ashley at Mission District from {mins_to_time(m[ashley_start].as_long())} to {mins_to_time(m[ashley_end].as_long())}")
        print(f"5. Travel to Nob Hill (12 min)")
        print(f"6. Meet Patricia at Nob Hill from {mins_to_time(m[patricia_start].as_long())} to {mins_to_time(m[patricia_end].as_long())}")
        return

    # Sequence 2: Timothy -> Patricia -> Ashley
    seq2 = Solver()
    seq2.add(s.assertions())
    seq2.add(timothy_start >= 8)  # Travel from Russian Hill to Embarcadero
    seq2.add(patricia_start >= timothy_end + travel[('Embarcadero', 'Nob Hill')])
    seq2.add(ashley_start >= patricia_end + travel[('Nob Hill', 'Mission District')])
    
    if seq2.check() == sat:
        m = seq2.model()
        print("SOLUTION:")
        print(f"1. Travel from Russian Hill to Embarcadero (8 min)")
        print(f"2. Meet Timothy at Embarcadero from {mins_to_time(m[timothy_start].as_long())} to {mins_to_time(m[timothy_end].as_long())}")
        print(f"3. Travel to Nob Hill (10 min)")
        print(f"4. Meet Patricia at Nob Hill from {mins_to_time(m[patricia_start].as_long())} to {mins_to_time(m[patricia_end].as_long())}")
        print(f"5. Travel to Mission District (13 min)")
        print(f"6. Meet Ashley at Mission District from {mins_to_time(m[ashley_start].as_long())} to {mins_to_time(m[ashley_end].as_long())}")
        return

    print("No feasible schedule found that meets all constraints.")

def mins_to_time(minutes):
    """Convert minutes since 9:00 AM to HH:MM format"""
    total_mins = 540 + minutes  # 9:00 AM is 540 minutes from midnight
    hours = total_mins // 60
    mins = total_mins % 60
    ampm = "AM" if hours < 12 else "PM"
    hours = hours % 12
    hours = 12 if hours == 0 else hours
    return f"{hours}:{mins:02d} {ampm}"

solve_scheduling()