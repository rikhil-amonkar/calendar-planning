import json
from z3 import *

def solve_puzzle():
    N = 5

    # Enumerations
    Names = ["Peter", "Arnold", "Eric", "Bob", "Alice"]
    Heights = ["average", "very tall", "very short", "short", "tall"]
    Cigars = ["prince", "dunhill", "blends", "pall mall", "blue master"]
    Smoothies = ["lime", "cherry", "dragonfruit", "watermelon", "desert"]
    Phones = ["oneplus 9", "samsung galaxy s21", "iphone 13", "huawei p50", "google pixel 6"]

    # Index helpers
    PETER, ARNOLD, ERIC, BOB, ALICE = range(5)
    AVERAGE, VERY_TALL, VERY_SHORT, SHORT, TALL = range(5)
    PRINCE, DUNHILL, BLENDS, PALL_MALL, BLUE_MASTER = range(5)
    LIME, CHERRY, DRAGONFRUIT, WATERMELON, DESERT = range(5)
    ONEPLUS9, SAMSUNG_S21, IPHONE13, HUAWEI_P50, PIXEL6 = range(5)

    # Variables: for each house (0..4), assign index of attribute 0..4
    name = [Int(f"name_{i}") for i in range(N)]
    height = [Int(f"height_{i}") for i in range(N)]
    cigar = [Int(f"cigar_{i}") for i in range(N)]
    smoothie = [Int(f"smoothie_{i}") for i in range(N)]
    phone = [Int(f"phone_{i}") for i in range(N)]

    s = Solver()

    # Domains
    for i in range(N):
        s.add(And(name[i] >= 0, name[i] < 5))
        s.add(And(height[i] >= 0, height[i] < 5))
        s.add(And(cigar[i] >= 0, cigar[i] < 5))
        s.add(And(smoothie[i] >= 0, smoothie[i] < 5))
        s.add(And(phone[i] >= 0, phone[i] < 5))

    # All-different for each category
    s.add(Distinct(name))
    s.add(Distinct(height))
    s.add(Distinct(cigar))
    s.add(Distinct(smoothie))
    s.add(Distinct(phone))

    # Helper functions
    def directly_left_of(arrA, valA, arrB, valB):
        return Or([And(arrA[i] == valA, arrB[i+1] == valB) for i in range(N-1)])

    def next_to(arrA, valA, arrB, valB):
        conds = []
        for i in range(N-1):
            conds.append(And(arrA[i] == valA, arrB[i+1] == valB))
            conds.append(And(arrB[i] == valB, arrA[i+1] == valA))
        return Or(conds)

    def two_apart_names(valLeft, valRight):
        # |pos(valLeft) - pos(valRight)| = 2
        conds = []
        for i in range(N):
            if i + 2 < N:
                conds.append(And(name[i] == valLeft, name[i+2] == valRight))
            if i - 2 >= 0:
                conds.append(And(name[i] == valLeft, name[i-2] == valRight))
        return Or(conds)

    def distance_three_height_smoothie(h_val, s_val):
        # |pos(height==h_val) - pos(smoothie==s_val)| = 3
        conds = []
        for i in range(N):
            if i + 3 < N:
                conds.append(And(height[i] == h_val, smoothie[i+3] == s_val))
            if i - 3 >= 0:
                conds.append(And(height[i] == h_val, smoothie[i-3] == s_val))
        return Or(conds)

    def left_of_smoothie(val_left, val_right):
        conds = []
        for i in range(N):
            for j in range(i+1, N):
                conds.append(And(smoothie[i] == val_left, smoothie[j] == val_right))
        return Or(conds)

    # Clues:

    # 1. The Prince smoker is the Desert smoothie lover.
    for i in range(N):
        s.add((cigar[i] == PRINCE) == (smoothie[i] == DESERT))

    # 2. There is one house between Eric and Alice.
    s.add(two_apart_names(ERIC, ALICE) or two_apart_names(ALICE, ERIC))

    # 3. The person who is short is the person who smokes many unique blends.
    for i in range(N):
        s.add((height[i] == SHORT) == (cigar[i] == BLENDS))

    # 4. The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    s.add(directly_left_of(phone, IPHONE13, cigar, BLUE_MASTER))

    # 5. The person who has an average height is the Dunhill smoker.
    for i in range(N):
        s.add((height[i] == AVERAGE) == (cigar[i] == DUNHILL))

    # 6. Eric is the person who is very tall.
    for i in range(N):
        s.add((name[i] == ERIC) == (height[i] == VERY_TALL))

    # 7. Arnold is directly left of the person who uses a Huawei P50.
    s.add(directly_left_of(name, ARNOLD, phone, HUAWEI_P50))

    # 8. Bob is not in the fourth house. (house index 3)
    s.add(name[3] != BOB)

    # 9. Eric is directly left of the person who likes Cherry smoothies.
    s.add(directly_left_of(name, ERIC, smoothie, CHERRY))

    # 10. Bob is the Dunhill smoker.
    for i in range(N):
        s.add((name[i] == BOB) == (cigar[i] == DUNHILL))

    # 11. The Dragonfruit smoothie lover is Bob.
    for i in range(N):
        s.add((name[i] == BOB) == (smoothie[i] == DRAGONFRUIT))

    # 12. The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    s.add(next_to(phone, IPHONE13, phone, ONEPLUS9))

    # 13. The person who uses a Samsung Galaxy S21 is the person who is short.
    for i in range(N):
        s.add((phone[i] == SAMSUNG_S21) == (height[i] == SHORT))

    # 14. There are two houses between the person who is very tall and the Dragonfruit smoothie lover.
    s.add(distance_three_height_smoothie(VERY_TALL, DRAGONFRUIT))

    # 15. The person who uses an iPhone 13 is Eric.
    for i in range(N):
        s.add((phone[i] == IPHONE13) == (name[i] == ERIC))

    # 16. The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    s.add(left_of_smoothie(DESERT, LIME))

    # 17. Arnold and the person who is very short are next to each other.
    s.add(next_to(name, ARNOLD, height, VERY_SHORT))

    if s.check() != sat:
        raise Exception("No solution found")

    m = s.model()

    def get_vals(arr, labels):
        return [labels[m[v].as_long()] for v in arr]

    names_out = get_vals(name, Names)
    heights_out = get_vals(height, Heights)
    cigars_out = get_vals(cigar, Cigars)
    smoothies_out = get_vals(smoothie, Smoothies)
    phones_out = get_vals(phone, Phones)

    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
            "rows": []
        }
    }

    for i in range(N):
        row = [
            str(i+1),
            names_out[i],
            heights_out[i],
            cigars_out[i],
            smoothies_out[i],
            phones_out[i]
        ]
        result["solution"]["rows"].append(row)

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))