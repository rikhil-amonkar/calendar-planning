def main():
    # Itinerary of overnight stays for 26 nights
    # Starts and ends at base camp (0)
    # Visits all 25 refuges, with base camp visited twice (start and end)
    stays = [
        0,  # base camp (0,0) - night0
        1,  # (0,1) - night1
        2,  # (0,2) - night2
        3,  # (0,3) - night3
        4,  # (0,4) - night4
        9,  # (1,4) - night5
        8,  # (1,3) - night6
        7,  # (1,2) - night7
        6,  # (1,1) - night8
        11, # (2,1) - night9
        12, # (2,2) - night10
        13, # (2,3) - night11
        14, # (2,4) - night12
        19, # (3,4) - night13
        18, # (3,3) - night14
        17, # (3,2) - night15
        16, # (3,1) - night16
        21, # (4,1) - night17
        22, # (4,2) - night18
        23, # (4,3) - night19
        24, # (4,4) - night20
        20, # (4,0) - night21
        15, # (3,0) - night22
        10, # (2,0) - night23
        5,  # (1,0) - night24
        0,  # base camp (0,0) - night25
    ]
    for refuge in stays:
        print(refuge)

if __name__ == "__main__":
    main()