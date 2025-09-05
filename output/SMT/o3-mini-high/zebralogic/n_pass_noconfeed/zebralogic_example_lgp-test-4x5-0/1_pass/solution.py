from z3 import *
import json

def main():
    s = Solver()

    # Define variables for houses (values 1..4)
    # Names
    Eric = Int('Eric')
    Peter = Int('Peter')
    Arnold = Int('Arnold')
    Alice = Int('Alice')
    # Smoothies
    dragonfruit = Int('dragonfruit')
    cherry = Int('cherry')
    desert = Int('desert')
    watermelon = Int('watermelon')
    # Cigars
    blue_master = Int('blue_master')
    pall_mall = Int('pall_mall')
    dunhill = Int('dunhill')
    prince = Int('prince')
    # Heights
    tall = Int('tall')
    average = Int('average')
    short = Int('short')
    very_short = Int('very_short')
    # Phone Models
    google_pixel6 = Int('google_pixel6')
    samsung_galaxy_s21 = Int('samsung_galaxy_s21')
    iphone_13 = Int('iphone_13')
    oneplus_9 = Int('oneplus_9')

    # List all variables for domain constraints.
    vars_list = [
        Eric, Peter, Arnold, Alice,
        dragonfruit, cherry, desert, watermelon,
        blue_master, pall_mall, dunhill, prince,
        tall, average, short, very_short,
        google_pixel6, samsung_galaxy_s21, iphone_13, oneplus_9
    ]
    for var in vars_list:
        s.add(And(var >= 1, var <= 4))

    # All items within each category must be in different houses.
    s.add(Distinct(Eric, Peter, Arnold, Alice))
    s.add(Distinct(dragonfruit, cherry, desert, watermelon))
    s.add(Distinct(blue_master, pall_mall, dunhill, prince))
    s.add(Distinct(tall, average, short, very_short))
    s.add(Distinct(google_pixel6, samsung_galaxy_s21, iphone_13, oneplus_9))

    # Clue 1: The Dragonfruit smoothie lover is Eric.
    s.add(dragonfruit == Eric)
    # Clue 2: The Dunhill smoker is the person who likes Cherry smoothies.
    s.add(dunhill == cherry)
    # Clue 3: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    s.add(samsung_galaxy_s21 + 1 == iphone_13)
    # Clue 4: The Dunhill smoker is somewhere to the right of the person who is very short.
    s.add(dunhill > very_short)
    # Clue 5: The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    s.add(watermelon > desert)
    # Clue 6: The Prince smoker is the person who uses a OnePlus 9.
    s.add(prince == oneplus_9)
    # Clue 7: The person who is tall is in the third house.
    s.add(tall == 3)
    # Clue 8: The person who is very short is the person who uses an iPhone 13.
    s.add(very_short == iphone_13)
    # Clue 9: The person who smokes Blue Master is not in the first house.
    s.add(blue_master != 1)
    # Clue 10: The Dunhill smoker is the person who is short.
    s.add(dunhill == short)
    # Clue 11: Peter is not in the third house.
    s.add(Peter != 3)
    # Clue 12: Arnold is the person who uses a Google Pixel 6.
    s.add(Arnold == google_pixel6)
    # Clue 13: The Dragonfruit smoothie lover is the person partial to Pall Mall.
    s.add(dragonfruit == pall_mall)

    if s.check() == sat:
        m = s.model()

        # Build a mapping for each house number (1 through 4) with empty attributes.
        houses_result = {i: {"Name": None, "Smoothie": None, "Cigar": None, "Height": None, "PhoneModel": None} for i in range(1, 5)}

        # Map names to their houses.
        names_map = {
            "Eric": m[Eric].as_long(),
            "Peter": m[Peter].as_long(),
            "Arnold": m[Arnold].as_long(),
            "Alice": m[Alice].as_long()
        }
        # Map smoothies.
        smoothies_map = {
            "dragonfruit": m[dragonfruit].as_long(),
            "cherry": m[cherry].as_long(),
            "desert": m[desert].as_long(),
            "watermelon": m[watermelon].as_long()
        }
        # Map cigars.
        cigars_map = {
            "blue master": m[blue_master].as_long(),
            "pall mall": m[pall_mall].as_long(),
            "dunhill": m[dunhill].as_long(),
            "prince": m[prince].as_long()
        }
        # Map heights.
        heights_map = {
            "tall": m[tall].as_long(),
            "average": m[average].as_long(),
            "short": m[short].as_long(),
            "very short": m[very_short].as_long()
        }
        # Map phone models.
        phones_map = {
            "google pixel 6": m[google_pixel6].as_long(),
            "samsung galaxy s21": m[samsung_galaxy_s21].as_long(),
            "iphone 13": m[iphone_13].as_long(),
            "oneplus 9": m[oneplus_9].as_long()
        }

        # Fill in the house mapping.
        for name, house in names_map.items():
            houses_result[house]["Name"] = name
        for smoothie, house in smoothies_map.items():
            houses_result[house]["Smoothie"] = smoothie
        for cigar, house in cigars_map.items():
            houses_result[house]["Cigar"] = cigar
        for height, house in heights_map.items():
            houses_result[house]["Height"] = height
        for phone, house in phones_map.items():
            houses_result[house]["PhoneModel"] = phone

        header = ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"]
        rows = []
        for i in range(1, 5):
            row = [
                str(i),
                houses_result[i]["Name"],
                houses_result[i]["Smoothie"],
                houses_result[i]["Cigar"],
                houses_result[i]["Height"],
                houses_result[i]["PhoneModel"]
            ]
            rows.append(row)

        output = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()