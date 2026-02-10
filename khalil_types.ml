type weight = Short | Long | SuperLong
type letter = Mutaharrik | Sakin
type conversion_result = ConvOk of weight list | ConvPreconditionFailed | ConvMalformedOutput
type foot = Faulun | Failun | Mafailun | Mustafilun | Failatun | Mafulatu | Mutafailun | Mufaalatun
type block = BlkSababKhafif | BlkSababThaqil | BlkWatadMajmu | BlkWatadMafruq
type meter = Tawil | Madid | Basit | Wafir | Kamil | Hazaj | Rajaz | Ramal
           | Sari | Munsarih | Khafif | Mudari | Muqtadab | Mujtathth
           | Mutaqarib | Mutadarik
type circle = Mukhtalifa | Mualifa | Mujtallaba | Mushtabaha | Muttafiqa
type zihaf = Khabn | Tayy | Qabd | Kaff | Waqs | Asb | Idmar | Aql | Shamm
type illa = Qat | Qasr | Hadhf | Tasbigh | Batr | Qatf | Tarfil | Tadhyil
          | Hadhadh | Salm | Kashf | Waqf | Tashith
type compound_zihaf = Khazl | Khabl | Shakl | Naqs
type foot_position = Hashw | Arud | Darb
type foot_annotation = Canonical | SimpleZihaf of zihaf | CompoundZihaf of compound_zihaf | Illa of illa
type scan_result = ScanSuccess of meter | ScanVariant of meter * foot_annotation list | ScanFailed
type rhyme_element = Rawiy | Wasl | Ridf | Tasis | Dakhil
type haraka = Damma | Fatha | Kasra
