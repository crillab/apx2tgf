# APX2TGF

APX2TGF is a tool dedicated to the translation of Argumentation Frameworks (AF) from the APX format to the TGF format. It provides a set of commands allowing the translation of frameworks, extensions and arguments.


## How does it works

Each command of APX2TGF take an input AF in the APX format, provided by the mandatory `-i` command line argument. Each argument in this AF is given an unique integer index, starting from `0` to the number of arguments minus 1, which becomes the TGF index of this argument. As the indexing algorithm is determinist, successive calls to APX2TGF will involve the same correspondence between the APX argument labels and the TGF argument indexes, which ensures the back-translations of TGF solver outputs into the APX formalism provided by this software will be correct.


## CLI help

APX2TGF general CLI help page can be seen by invoking `apx2tgf -h`. This help page mainly prints generalities about the software and its available subcommands. To get help for a subcommand `SUB`, just invoke `apx2tgf SUB -h`.


## Translating an APX framework

Translating an APX framework is realized by the `framework` command.

```text
me@machine:~/apx2tgf$ cat ./instance.apx
arg(a0).
arg(a1).
arg(a2).
att(a0,a0).
att(a0,a1).

me@machine:~/apx2tgf$ apx2tgf framework -i ./instance.apx -o ./instance.tgf 
[INFO ] [2021-04-27 11:09:29] apx2tgf 0.1.0
[INFO ] [2021-04-27 11:09:29] reading input file /home/me/apx2tgf/instance.apx
[INFO ] [2021-04-27 11:09:29] setting output file to /home/me/apx2tgf/instance.tgf
[INFO ] [2021-04-27 11:09:29] exiting successfully after 2.364846ms

me@machine:~/apx2tgf$ cat instance.tgf 
0
1
2
#
0 0
0 1
```

You can now use a TGF solver with `instance.tgf`. In case the problem under consideration is an acceptance check, you also need to translate the argument under consideration to feed the solver, using the `argument` command.


## Translating an argument from APX to TGF

Translating an argument from APX to TGF is done with the `argument` command.
This command needs the input AF (given by the `-i` argument), and one of its arguments provided by the `-a` option.

```text
me@machine:~/apx2tgf$ apx2tgf argument -i ./instance.apx -a a1
[INFO ] [2021-04-27 11:16:09] apx2tgf 0.1.0
[INFO ] [2021-04-27 11:16:09] reading input file /home/me/apx2tgf/instance.apx
[INFO ] [2021-04-27 11:16:09] setting output to STDOUT
1
[INFO ] [2021-04-27 11:16:09] exiting successfully after 2.239224ms
```

The TGF index is given by the line that does not begin with a bracket.
In case you don't want to clean the output, you can put this index in an output file with the `-o` option.


## Translating back TGF solver results to the APX format

For most of the queries involved in ICCMA'21 competitions, the output of the TGF solver may be used without any translation. However, when the query concerns the output of an extension and such an extension exists, it may be useful to translate the TGF-formatted extension into the APX format.

This can be done by the `extension` command, fed with the input AF (given by the `-i` argument) and a file containing the TGF extension (given by the `-e` argument). Again, the output may be clean or stored into a file given by the `-o` option.

```text
me@machine:~/apx2tgf$$ cat ext.tgf 
[0]

me@machine:~/apx2tgf$$ ./apx2tgf.bin extension -i ./instance.apx -e ./ext.tgf -o ./ext.apx
[INFO ] [2021-04-27 11:26:28] apx2tgf 0.1.0
[INFO ] [2021-04-27 11:26:28] reading input file /home/me/apx2tgf/instance.apx
[INFO ] [2021-04-27 11:26:28] setting output file to /home/me/apx2tgf/ext.apx
[INFO ] [2021-04-27 11:26:28] exiting successfully after 2.522048ms

me@machine:~/apx2tgf$$ cat ext.apx 
[a0]
```


## License

APX2TGF is developed at CRIL (Centre de Recherche en Informatique de Lens).
It is made available under the terms of the GNU GPLv3 license.
