from z3 import *

def main():
    opt = Optimize()
    # Variables
    D_Sunset = Int('D_Sunset')  # Departure time from Sunset (minutes since midnight)
    D_GG = Int('D_GG')          # Departure time from Golden Gate Park
    A_GG = D_Sunset + 11        # Arrival at Golden Gate Park

    # Constraints
    opt.add(D_Sunset >= 540)    # Can't leave Sunset before 9:00 AM (540 minutes)
    opt.add(D_GG >= A_GG)       # Can't leave Golden Gate Park before arriving

    # Calculate overlap with Joshua's availability (1245 to 1305 minutes)
    overlap_start = If(A_GG > 1245, A_GG, 1245)
    overlap_end = If(D_GG < 1305, D_GG, 1305)
    overlap = overlap_end - overlap_start
    # Ensure at least 15 minutes overlap
    opt.add(If(And(A_GG < 1305, D_GG > 1245), overlap >= 15, False)

    # Optimize to leave Golden Gate as early as possible (maximize time elsewhere)
    opt.minimize(D_GG)

    if opt.check() == sat:
        m = opt.model()
        depart_sunset = m.eval(D_Sunset).as_long()
        depart_gg = m.eval(D_GG).as_long()
        arrive_gg = depart_sunset + 11
        return_sunset = depart_gg + 10

        # Print results in HH:MM format
        def fmt(time):
            h, m = divmod(time, 60)
            return f"{h:02}:{m:02}"

        print(f"Depart Sunset: {fmt(depart_sunset)}")
        print(f"Arrive Golden Gate Park: {fmt(arrive_gg)}")
        print(f"Depart Golden Gate Park: {fmt(depart_gg)}")
        print(f"Return to Sunset: {fmt(return_sunset)}")
    else:
        print("No valid schedule found.")

if __name__ == "__main__":
    main()