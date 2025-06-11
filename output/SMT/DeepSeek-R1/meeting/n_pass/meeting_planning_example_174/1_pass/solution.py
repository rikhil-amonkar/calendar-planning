from z3 import *

def min_to_time(m):
    h = m // 60
    m_min = m % 60
    if h == 0 or h == 12:
        hour_str = "12"
    else:
        hour_str = str(h % 12)
    suffix = "AM" if h < 12 else "PM"
    return f"{hour_str}:{m_min:02d}{suffix}"

# Case 1: Meet both friends (Kenneth then Thomas)
s1 = Solver()
L0 = Int('L0')
S1 = Int('S1')
S2 = Int('S2')

A1 = L0 + 13  # Arrival at Mission District
E1 = S1 + 45  # End of meeting with Kenneth
A2 = E1 + 16  # Arrival at Pacific Heights
E2 = S2 + 75  # End of meeting with Thomas

s1.add(L0 >= 540)     # Leave Nob Hill after 9:00 AM
s1.add(S1 >= A1)      # Meeting Kenneth starts after arrival
s1.add(S1 >= 720)     # Meeting Kenneth starts after 12:00 PM
s1.add(E1 <= 945)     # Meeting Kenneth ends by 3:45 PM
s1.add(S2 >= A2)      # Meeting Thomas starts after arrival at Pacific Heights
s1.add(S2 >= 930)     # Meeting Thomas starts after 3:30 PM
s1.add(E2 <= 1155)    # Meeting Thomas ends by 7:15 PM

if s1.check() == sat:
    model = s1.model()
    L0_val = model[L0].as_long()
    S1_val = model[S1].as_long()
    S2_val = model[S2].as_long()
    E1_val = S1_val + 45
    A2_val = E1_val + 16
    E2_val = S2_val + 75
    print("SOLUTION: We can meet both friends.")
    print(f"Start at Nob Hill at 9:00AM.")
    print(f"Leave Nob Hill at {min_to_time(L0_val)}.")
    print(f"Travel to Mission District (13 minutes), arrive at {min_to_time(L0_val + 13)}.")
    print(f"Meet Kenneth from {min_to_time(S1_val)} to {min_to_time(E1_val)}.")
    print(f"Leave Mission District at {min_to_time(E1_val)}.")
    print(f"Travel to Pacific Heights (16 minutes), arrive at {min_to_time(A2_val)}.")
    print(f"Meet Thomas from {min_to_time(S2_val)} to {min_to_time(E2_val)}.")
else:
    # Case 2: Meet only Kenneth
    s2 = Solver()
    L0_k = Int('L0_k')
    S1_k = Int('S1_k')
    A1_k = L0_k + 13
    E1_k = S1_k + 45
    s2.add(L0_k >= 540)
    s2.add(S1_k >= A1_k)
    s2.add(S1_k >= 720)
    s2.add(E1_k <= 945)
    if s2.check() == sat:
        model = s2.model()
        L0_val = model[L0_k].as_long()
        S1_val = model[S1_k].as_long()
        E1_val = S1_val + 45
        print("SOLUTION: We can meet only Kenneth.")
        print(f"Start at Nob Hill at 9:00AM.")
        print(f"Leave Nob Hill at {min_to_time(L0_val)}.")
        print(f"Travel to Mission District (13 minutes), arrive at {min_to_time(L0_val + 13)}.")
        print(f"Meet Kenneth from {min_to_time(S1_val)} to {min_to_time(E1_val)}.")
    else:
        # Case 3: Meet only Thomas
        s3 = Solver()
        L0_t = Int('L0_t')
        S2_t = Int('S2_t')
        A1_t = L0_t + 8
        E2_t = S2_t + 75
        s3.add(L0_t >= 540)
        s3.add(S2_t >= A1_t)
        s3.add(S2_t >= 930)
        s3.add(E2_t <= 1155)
        if s3.check() == sat:
            model = s3.model()
            L0_val = model[L0_t].as_long()
            S2_val = model[S2_t].as_long()
            E2_val = S2_val + 75
            print("SOLUTION: We can meet only Thomas.")
            print(f"Start at Nob Hill at 9:00AM.")
            print(f"Leave Nob Hill at {min_to_time(L0_val)}.")
            print(f"Travel to Pacific Heights (8 minutes), arrive at {min_to_time(L0_val + 8)}.")
            print(f"Meet Thomas from {min_to_time(S2_val)} to {min_to_time(E2_val)}.")
        else:
            print("SOLUTION: Cannot meet any friend.")