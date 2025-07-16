from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Convert all times to minutes since midnight
    arrival_time = 9 * 60       # 9:00 AM (540 minutes)
    emily_start_min = 16 * 60   # 4:00 PM (960 minutes)
    emily_end_max = 17 * 60 + 15  # 5:15 PM (1035 minutes)
    margaret_start_min = 19 * 60  # 7:00 PM (1140 minutes)
    margaret_end_max = 21 * 60    # 9:00 PM (1260 minutes)

    # Meeting time variables (minutes since midnight)
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')

    # Travel times (minutes)
    NB_to_US = 7    # North Beach to Union Square
    US_to_RH = 13   # Union Square to Russian Hill

    # Meeting duration constraints
    s.add(emily_start >= emily_start_min)
    s.add(emily_end <= emily_end_max)
    s.add(emily_end - emily_start >= 45)  # At least 45 minutes with Emily
    
    s.add(margaret_start >= margaret_start_min)
    s.add(margaret_end <= margaret_end_max)
    s.add(margaret_end - margaret_start >= 120)  # At least 2 hours with Margaret

    # Travel constraints
    s.add(emily_start >= arrival_time + NB_to_US)  # Time to reach Union Square
    s.add(margaret_start >= emily_end + US_to_RH)  # Time to reach Russian Hill

    # Maximize total meeting time
    total_time = (emily_end - emily_start) + (margaret_end - margaret_start)
    s.maximize(total_time)

    # Check solution and format output
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule Found:")
        print(f"1. Meet Emily at Union Square:")
        print(f"   Start: {m[emily_start].as_long()//60}:{m[emily_start].as_long()%60:02d}")
        print(f"   End:   {m[emily_end].as_long()//60}:{m[emily_end].as_long()%60:02d}")
        print(f"   Duration: {m[emily_end].as_long() - m[emily_start].as_long()} minutes")
        print(f"\n2. Travel to Russian Hill (13 minutes)")
        print(f"\n3. Meet Margaret at Russian Hill:")
        print(f"   Start: {m[margaret_start].as_long()//60}:{m[margaret_start].as_long()%60:02d}")
        print(f"   End:   {m[margaret_end].as_long()//60}:{m[margaret_end].as_long()%60:02d}")
        print(f"   Duration: {m[margaret_end].as_long() - m[margaret_start].as_long()} minutes")
        print(f"\nTotal time with friends: {m[emily_end].as_long() - m[emily_start].as_long() + m[margaret_end].as_long() - m[margaret_start].as_long()} minutes")
    else:
        print("No valid schedule exists that meets all constraints.")

solve_scheduling()